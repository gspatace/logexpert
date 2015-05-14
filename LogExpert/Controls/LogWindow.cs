using System.Diagnostics;
using LogExpert.Interfaces;
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using LogExpert.Dialogs;
using System.Text.RegularExpressions;
using System.Runtime.Remoting.Messaging;
using System.Threading;
using System.IO;
using System.Globalization;
using System.Reflection;
using System.Collections;
using WeifenLuo.WinFormsUI.Docking;
using System.Linq;

namespace LogExpert
{
    public partial class LogWindow : DockContent, ILogPaintContext, ILogView, ILogWindowSearch
    {
        static List<string> IgnoreStackTraceFilePatterns = new List<string>()
        {
            @"UnityPreBuilt\\Zenject",
            @"UnityPreBuilt\\Debugging",
            @"UnityPreBuilt\\DebuggingUnity",
        };

        static Regex _stackTraceIgnoreRegex;

        static Regex StackTraceIgnoreRegex
        {
            get
            {
                if (_stackTraceIgnoreRegex == null)
                {
                    _stackTraceIgnoreRegex = TryBuildRegex(IgnoreStackTraceFilePatterns);
                }

                return _stackTraceIgnoreRegex;
            }
        }


        public static Regex TryBuildRegex(List<string> patterns)
        {
            if (patterns.Count == 0)
            {
                return null;
            }

            string fullPattern = "";

            foreach (var pattern in patterns)
            {
                if (fullPattern.Length > 0)
                {
                    fullPattern += "|";
                }

                fullPattern += pattern;
            }

            return new Regex(fullPattern, RegexOptions.Singleline);
        }

        const int MAX_HISTORY = 30;
        const int MAX_COLUMNIZER_HISTORY = 40;
        const int SPREAD_MAX = 99;
        const int PROGRESS_BAR_MODULO = 1000;
        const int FILTER_ADCANCED_SPLITTER_DISTANCE = 54;

        Classes.FuzzyBlockDetection _fuzzyBlockDetection = new Classes.FuzzyBlockDetection();

        ILogLineColumnizer _forcedColumnizer;
        List<HilightEntry> _tempHilightEntryList = new List<HilightEntry>();
        readonly Object _tempHilightEntryListLock = new Object();
        HilightGroup _currentHighlightGroup = new HilightGroup();
        readonly Object _currentHighlightGroupLock = new Object();
        FilterParams _filterParams = new FilterParams();
        SearchParams _currentSearchParams = null;
        List<int> _filterResultList = new List<int>();
        List<int> _lastFilterLinesList = new List<int>();
        List<int> _filterHitList = new List<int>();
        readonly Object _bookmarkLock = new Object();

        int _filterPipeNameCounter = 0;
        readonly Dictionary<Control, bool> _freezeStateMap = new Dictionary<Control, bool>();

        EventWaitHandle _filterUpdateEvent = new ManualResetEvent(false);

        DelayedTrigger _selectionChangedTrigger = new DelayedTrigger(200);

        IList<BackgroundProcessCancelHandler> _cancelHandlerList = new List<BackgroundProcessCancelHandler>();

        readonly EventWaitHandle _loadingFinishedEvent = new ManualResetEvent(false);
        readonly EventWaitHandle _externaLoadingFinishedEvent = new ManualResetEvent(false);
        // used for external wait fx WaitForLoadFinished()

        bool _waitingForClose = false;
        bool _isSearching = false;

        bool _showAdvanced = false;
        bool _isErrorShowing = false;
        bool _isTimestampDisplaySyncing = false;
        bool _shouldTimestampDisplaySyncingCancel = false;
        bool _isDeadFile = false;
        bool _noSelectionUpdates = false;
        bool _shouldCallTimeSync = false;

        int _lineHeight = 0;
        int _reloadOverloadCounter = 0;
        readonly Object _reloadLock = new Object();
        int _selectedCol = 0;
        // set by context menu event for column headers only


        readonly Thread _timeshiftSyncThread = null;
        readonly EventWaitHandle _timeshiftSyncWakeupEvent = new ManualResetEvent(false);
        readonly EventWaitHandle _timeshiftSyncTimerEvent = new ManualResetEvent(false);
        int _timeshiftSyncLine = 0;

        PatternWindow _patternWindow;
        PatternArgs _patternArgs = new PatternArgs();

        Image _advancedButtonImage;
        Image _searchButtonImage;

        Image _panelOpenButtonImage;
        Image _panelCloseButtonImage;

        Object _timeSyncListLock = new Object();

        Font _normalFont;
        Font _fontBold;
        Font _fontMonospaced;

        public BookmarkDataProvider BookmarkProvider { get; private set; }

        public event Action<ProgressEventArgs> ProgressBarUpdate;

        protected ILogLineColumnizer _forcedColumnizerForLoading;

        protected ILogLineColumnizer _currentColumnizer;
        protected readonly Object _currentColumnizerLock = new Object();

        private readonly Thread _logEventHandlerThread = null;
        protected readonly EventWaitHandle _logEventArgsEvent = new ManualResetEvent(false);
        protected readonly List<LogEventArgs> _logEventArgsList = new List<LogEventArgs>();

        protected readonly GuiStateArgs _guiStateArgs = new GuiStateArgs();

        protected SortedList<int, RowHeightEntry> _rowHeightList = new SortedList<int, RowHeightEntry>();

        protected readonly IList<FilterPipe> _filterPipeList = new List<FilterPipe>();

        protected TimeSpreadCalculator _timeSpreadCalc;

        protected readonly StatusLineEventArgs _statusEventArgs = new StatusLineEventArgs();
        protected readonly ProgressEventArgs _progressEventArgs = new ProgressEventArgs();

        protected DelayedTrigger _statusLineTrigger = new DelayedTrigger(200);

        protected bool _shouldCancel = false;
        protected bool _isLoading;
        protected bool _isLoadError = false;

        protected MultifileOptions _multifileOptions = new MultifileOptions();
        protected ReloadMemento _reloadMemento;
        protected string[] _fileNames;

        protected LogTabWindow _parentLogTabWin;
        protected ColumnCache _columnCache = new ColumnCache();

        public LogfileReader CurrentLogFileReader { get; protected set; }

        public string FileName { get; protected set; }

        protected EncodingOptions EncodingOptions { get; set; }

        public LogWindow(LogTabWindow parent, string fileName, bool isTempFile, bool forcePersistenceLoading)
        {
            _logEventHandlerThread = new Thread(new ThreadStart(LogEventWorker));
            _logEventHandlerThread.IsBackground = true;
            _logEventHandlerThread.Start();

            BookmarkProvider = new BookmarkDataProvider();

            BookmarkColor = Color.FromArgb(165, 200, 225);
            TempTitleName = "";
            SuspendLayout();

            InitializeComponent();

            columnNamesLabel.Text = ""; // no filtering on columns by default

            _parentLogTabWin = parent;
            IsTempFile = isTempFile;
            ColumnizerCallbackObject = new ColumnizerCallback(this);

            FileName = fileName;
            ForcePersistenceLoading = forcePersistenceLoading;

            selectedDataGridView.DefaultCellStyle.WrapMode = DataGridViewTriState.True;
            selectedDataGridView.DefaultCellStyle.Alignment = DataGridViewContentAlignment.TopLeft;
            selectedDataGridView.AutoSizeRowsMode = DataGridViewAutoSizeRowsMode.AllCells;

            selectedDataGridView.SelectionChanged += selectedDataGridView_SelectionChanged;

            dataGridView.CellValueNeeded += DataGridView_CellValueNeeded;
            dataGridView.CellPainting += DataGridView_CellPainting;
            dataGridView.SelectionChanged += DataGridView_NewSelectionChanged;
            dataGridView.DoubleClick += DataGridView_DoubleClick;

            filterGridView.CellValueNeeded += FilterGridView_CellValueNeeded;
            filterGridView.CellPainting += FilterGridView_CellPainting;

            Closing += LogWindow_Closing;
            Disposed += LogWindow_Disposed;

            _timeSpreadCalc = new TimeSpreadCalculator(this);
            timeSpreadingControl1.TimeSpreadCalc = _timeSpreadCalc;
            timeSpreadingControl1.LineSelected += TimeSpreadingControl1_LineSelected;
            tableLayoutPanel1.ColumnStyles[1].SizeType = SizeType.Absolute;
            tableLayoutPanel1.ColumnStyles[1].Width = 20;
            tableLayoutPanel1.ColumnStyles[0].SizeType = SizeType.Percent;
            tableLayoutPanel1.ColumnStyles[0].Width = 100;

            _parentLogTabWin.HighlightSettingsChanged += Parent_HighlightSettingsChanged;

            SetColumnizer(PluginRegistry.GetInstance().RegisteredColumnizers[0]);

            _patternArgs.maxMisses = 5;
            _patternArgs.minWeight = 1;
            _patternArgs.maxDiffInBlock = 5;
            _patternArgs.fuzzy = 5;

            _filterParams = new FilterParams();
            foreach (string item in ConfigManager.Settings.filterHistoryList)
            {
                filterComboBox.Items.Add(item);
            }
            filterRegexCheckBox.Checked = _filterParams.isRegex;
            filterCaseSensitiveCheckBox.Checked = _filterParams.isCaseSensitive;
            filterTailCheckBox.Checked = _filterParams.isFilterTail;

            splitContainer1.Panel2Collapsed = true;
            advancedFilterSplitContainer.SplitterDistance = FILTER_ADCANCED_SPLITTER_DISTANCE;

            _timeshiftSyncThread = new Thread(SyncTimestampDisplayWorker);
            _timeshiftSyncThread.IsBackground = true;
            _timeshiftSyncThread.Start();

            _advancedButtonImage = advancedButton.Image;
            _searchButtonImage = filterSearchButton.Image;
            filterSearchButton.Image = null;

            dataGridView.EditModeMenuStrip = editModeContextMenuStrip;
            markEditModeToolStripMenuItem.Enabled = true;


            _panelOpenButtonImage = new Bitmap(GetType(), "Resources.PanelOpen.gif");
            _panelCloseButtonImage = new Bitmap(GetType(), "Resources.PanelClose.gif");

            Settings settings = ConfigManager.Settings;
            if (settings.appBounds != null && settings.appBounds.Right > 0)
            {
                Bounds = settings.appBounds;
            }

            _waitingForClose = false;
            dataGridView.Enabled = false;
            dataGridView.ColumnDividerDoubleClick += DataGridView_ColumnDividerDoubleClick;
            ShowAdvancedFilterPanel(false);
            filterKnobControl1.MinValue = 0;
            filterKnobControl1.MaxValue = SPREAD_MAX;
            filterKnobControl1.ValueChanged += FilterKnobControl1_CheckForFilterDirty;
            filterKnobControl2.MinValue = 0;
            filterKnobControl2.MaxValue = SPREAD_MAX;
            filterKnobControl2.ValueChanged += FilterKnobControl1_CheckForFilterDirty;
            fuzzyKnobControl.MinValue = 0;
            fuzzyKnobControl.MaxValue = 10;
            ToggleHighlightPanel(false); // hidden

            BookmarkProvider.BookmarkAdded += BookmarkProvider_BookmarkAdded;
            BookmarkProvider.BookmarkRemoved += BookmarkProvider_BookmarkRemoved;

            ResumeLayout();

            _statusLineTrigger.Signal += StatusLineTrigger_Signal;
            _selectionChangedTrigger.Signal += SelectionChangedTrigger_Signal;

            PreferencesChanged(_parentLogTabWin.Preferences, true, SettingsFlags.GuiOrColors);
        }



        public Color BookmarkColor { get; set; }

        public string TempTitleName { get; set; }

        public string Title
        {
            get
            {
                if (IsTempFile)
                {
                    return TempTitleName;
                }
                else
                {
                    return FileName;
                }
            }
        }

        public ColumnizerCallback ColumnizerCallbackObject { get; set; }

        public bool ForcePersistenceLoading { get; set; }

        // file name of given file used for loading (maybe logfile or lxp)
        public string GivenFileName { get; set; }

        public TimeSyncList TimeSyncList { get; set; }

        public bool IsTimeSynced
        {
            get
            {
                return TimeSyncList != null;
            }
        }

        internal FilterPipe FilterPipe { get; set; }



        public string SavePersistenceData(bool force)
        {
            if (!force)
            {
                if (!Preferences.saveSessions)
                {
                    return null;
                }
            }

            if (IsTempFile || _isLoadError)
            {
                return null;
            }

            try
            {
                PersistenceData persistenceData = GetPersistenceData();
                if (ForcedPersistenceFileName == null)
                {
                    return Persister.SavePersistenceData(FileName, persistenceData, Preferences);
                }
                else
                {
                    return Persister.SavePersistenceDataWithFixedName(ForcedPersistenceFileName, persistenceData);
                }
            }
            catch (IOException ex)
            {
                Logger.logError("Error saving persistence: " + ex.Message);
            }
            catch (Exception e)
            {
                MessageBox.Show("Unexpected error while saving persistence: " + e.Message);
            }
            return null;
        }

        public PersistenceData GetPersistenceData()
        {
            PersistenceData persistenceData = new PersistenceData();
            persistenceData.bookmarkList = BookmarkProvider.BookmarkList;
            persistenceData.rowHeightList = _rowHeightList;
            persistenceData.multiFile = IsMultiFile;
            persistenceData.multiFilePattern = _multifileOptions.FormatPattern;
            persistenceData.multiFileMaxDays = _multifileOptions.MaxDayTry;
            persistenceData.currentLine = dataGridView.CurrentCellAddress.Y;
            persistenceData.firstDisplayedLine = dataGridView.FirstDisplayedScrollingRowIndex;
            persistenceData.filterVisible = !splitContainer1.Panel2Collapsed;
            persistenceData.filterAdvanced = !advancedFilterSplitContainer.Panel1Collapsed;
            persistenceData.filterPosition = splitContainer1.SplitterDistance;
            persistenceData.followTail = _guiStateArgs.FollowTail;
            persistenceData.fileName = FileName;
            persistenceData.tabName = Text;
            persistenceData.columnizerName = CurrentColumnizer.GetName();
            persistenceData.lineCount = CurrentLogFileReader.LineCount;
            _filterParams.isFilterTail = filterTailCheckBox.Checked; // this option doesnt need a press on 'search'
            if (Preferences.saveFilters)
            {
                List<FilterParams> filterList = new List<FilterParams>();
                filterList.Add(_filterParams);
                persistenceData.filterParamsList = filterList;

                foreach (FilterPipe filterPipe in _filterPipeList)
                {
                    FilterTabData data = new FilterTabData();
                    data.persistenceData = filterPipe.OwnLogWindow.GetPersistenceData();
                    data.filterParams = filterPipe.FilterParams;
                    persistenceData.filterTabDataList.Add(data);
                }
            }
            if (_currentHighlightGroup != null)
            {
                persistenceData.highlightGroupName = _currentHighlightGroup.GroupName;
            }
            if (_fileNames != null && IsMultiFile)
            {
                persistenceData.multiFileNames.AddRange(_fileNames);
            }
            //persistenceData.showBookmarkCommentColumn = bookmarkWindow.ShowBookmarkCommentColumn;
            persistenceData.filterSaveListVisible = !highlightSplitContainer.Panel2Collapsed;
            persistenceData.encoding = CurrentLogFileReader.CurrentEncoding;
            return persistenceData;
        }

        public void WaitForLoadingFinished()
        {
            _externaLoadingFinishedEvent.WaitOne();
        }

        public void CloseLogWindow()
        {
            StopTimespreadThread();
            StopTimestampSyncThread();
            StopLogEventWorkerThread();
            _statusLineTrigger.Stop();
            _selectionChangedTrigger.Stop();
            _shouldCancel = true;
            if (CurrentLogFileReader != null)
            {
                UnRegisterLogFileReaderEvents();
                CurrentLogFileReader.StopMonitoringAsync();
            }
            if (_isLoading)
            {
                _waitingForClose = true;
            }
            if (IsTempFile)
            {
                Logger.logInfo("Deleting temp file " + FileName);
                try
                {
                    File.Delete(FileName);
                }
                catch (IOException e)
                {
                    Logger.logError("Error while deleting temp file " + FileName + ": " + e.ToString());
                }
            }
            if (FilterPipe != null)
            {
                FilterPipe.CloseAndDisconnect();
            }
            DisconnectFilterPipes();
        }

        public void ForceColumnizer(ILogLineColumnizer columnizer)
        {
            _forcedColumnizer = Util.CloneColumnizer(columnizer);
            SetColumnizer(_forcedColumnizer);
        }

        public void ForceColumnizerForLoading(ILogLineColumnizer columnizer)
        {
            _forcedColumnizerForLoading = Util.CloneColumnizer(columnizer);
        }

        public void ColumnizerConfigChanged()
        {
            SetColumnizerInternal(CurrentColumnizer);
        }

        public void SetColumnizer(ILogLineColumnizer columnizer, DataGridView gridView)
        {
            int rowCount = gridView.RowCount;
            int currLine = gridView.CurrentCellAddress.Y;
            int currFirstLine = gridView.FirstDisplayedScrollingRowIndex;

            gridView.Columns.Clear();

            DataGridViewTextBoxColumn markerColumn = new DataGridViewTextBoxColumn();
            markerColumn.HeaderText = "";
            markerColumn.AutoSizeMode = DataGridViewAutoSizeColumnMode.NotSet;
            markerColumn.Resizable = DataGridViewTriState.False;
            markerColumn.DividerWidth = 1;
            markerColumn.ReadOnly = true;
            markerColumn.HeaderCell.ContextMenuStrip = columnContextMenuStrip;
            gridView.Columns.Add(markerColumn);

            DataGridViewTextBoxColumn lineNumberColumn = new DataGridViewTextBoxColumn();
            lineNumberColumn.HeaderText = "Line";
            lineNumberColumn.AutoSizeMode = DataGridViewAutoSizeColumnMode.NotSet;
            lineNumberColumn.Resizable = DataGridViewTriState.NotSet;
            lineNumberColumn.DividerWidth = 1;
            lineNumberColumn.ReadOnly = true;
            lineNumberColumn.HeaderCell.ContextMenuStrip = columnContextMenuStrip;
            gridView.Columns.Add(lineNumberColumn);

            foreach (string colName in columnizer.GetColumnNames())
            {
                DataGridViewColumn titleColumn = new LogTextColumn();
                titleColumn.HeaderText = colName;
                titleColumn.AutoSizeMode = DataGridViewAutoSizeColumnMode.NotSet;
                titleColumn.Resizable = DataGridViewTriState.NotSet;
                titleColumn.DividerWidth = 1;
                titleColumn.HeaderCell.ContextMenuStrip = columnContextMenuStrip;
                gridView.Columns.Add(titleColumn);
            }

            columnNamesLabel.Text = CalculateColumnNames(_filterParams);

            gridView.RowCount = rowCount;
            if (currLine != -1)
            {
                gridView.CurrentCell = gridView.Rows[currLine].Cells[0];
            }
            if (currFirstLine != -1)
            {
                gridView.FirstDisplayedScrollingRowIndex = currFirstLine;
            }
            gridView.Refresh();
            AutoResizeColumns(gridView);
            ApplyFrozenState(gridView);
        }

        public string GetCellValue(int rowIndex, int columnIndex)
        {
            if (columnIndex == 1)
            {
                return (rowIndex + 1).ToString();   // line number
            }
            if (columnIndex != 0)   // marker column
            {
                try
                {
                    string[] cols = GetColumnsForLine(rowIndex);
                    if (cols != null)
                    {
                        if (columnIndex <= cols.Length + 1)
                        {
                            string value = cols[columnIndex - 2];
                            if (value != null)
                            {
                                value = value.Replace("\t", "  ");
                            }
                            return value;
                        }
                        else
                        {
                            if (columnIndex == 2)
                            {
                                return cols[cols.Length - 1].Replace("\t", "  ");
                            }
                        }
                    }
                }
                catch (Exception)
                {
                    //nothing
                }
            }
            return "";
        }

        /**
         * Returns the first HilightEntry that matches the given line
         */
        public HilightEntry FindHilightEntry(string line, bool noWordMatches)
        {
            // first check the temp entries
            lock (_tempHilightEntryListLock)
            {
                foreach (HilightEntry entry in _tempHilightEntryList)
                {
                    if (noWordMatches && entry.IsWordMatch)
                    {
                        continue;
                    }
                    if (CheckHighlightEntryMatch(entry, line))
                    {
                        return entry;
                    }
                }
            }

            lock (_currentHighlightGroupLock)
            {
                foreach (HilightEntry entry in _currentHighlightGroup.HilightEntryList)
                {
                    if (noWordMatches && entry.IsWordMatch)
                    {
                        continue;
                    }
                    if (CheckHighlightEntryMatch(entry, line))
                    {
                        return entry;
                    }
                }
                return null;
            }
        }

        public IList<HilightMatchEntry> FindHilightMatches(string line)
        {
            IList<HilightMatchEntry> resultList = new List<HilightMatchEntry>();
            if (line != null)
            {
                lock (_currentHighlightGroupLock)
                {
                    GetHighlightEntryMatches(line, _currentHighlightGroup.HilightEntryList, resultList);
                }
                lock (_tempHilightEntryList)
                {
                    GetHighlightEntryMatches(line, _tempHilightEntryList, resultList);
                }
            }
            return resultList;
        }

        public void GotoLine(int line)
        {
            if (line >= 0)
            {
                if (line < dataGridView.RowCount)
                {
                    SelectLine(line, false);
                }
                else
                {
                    SelectLine(dataGridView.RowCount - 1, false);
                }
                dataGridView.Focus();
            }
        }

        public void StartSearch()
        {
            _guiStateArgs.MenuEnabled = false;
            GuiStateUpdate(this, _guiStateArgs);
            SearchParams searchParams = _parentLogTabWin.SearchParams;
            if ((searchParams.isForward || searchParams.isFindNext) && !searchParams.isShiftF3Pressed)
            {
                searchParams.currentLine = dataGridView.CurrentCellAddress.Y + 1;
            }
            else
            {
                searchParams.currentLine = dataGridView.CurrentCellAddress.Y - 1;
            }

            _currentSearchParams = searchParams;    // remember for async "not found" messages

            _isSearching = true;
            _shouldCancel = false;

            StartProgressBar(dataGridView.RowCount, "Searching... Press ESC to cancel.");

            Func<SearchParams, int> searchFx = new Func<SearchParams, int>(Search);
            searchFx.BeginInvoke(searchParams, SearchComplete, null);

            RemoveAllSearchHighlightEntries();
            AddSearchHitHighlightEntry(searchParams);
        }

        public void FollowTailChanged(bool isChecked, bool byTrigger)
        {
            _guiStateArgs.FollowTail = isChecked;

            if (_guiStateArgs.FollowTail && CurrentLogFileReader != null)
            {
                if (dataGridView.RowCount >= CurrentLogFileReader.LineCount && CurrentLogFileReader.LineCount > 0)
                {
                    dataGridView.FirstDisplayedScrollingRowIndex = CurrentLogFileReader.LineCount - 1;
                }
            }
            BeginInvoke(new MethodInvoker(dataGridView.Refresh));
            //dataGridView.Refresh();
            _parentLogTabWin.FollowTailChanged(this, isChecked, byTrigger);
            SendGuiStateUpdate();
        }

        public void SelectLogLine(int line)
        {
            Invoke(new Action<int, bool>(SelectLine), new object[] { line, true });
        }

        public void SelectAndEnsureVisible(int line, bool triggerSyncCall)
        {
            try
            {
                SelectLine(line, triggerSyncCall, false);

                if (line < dataGridView.FirstDisplayedScrollingRowIndex ||
                    line > dataGridView.FirstDisplayedScrollingRowIndex + dataGridView.DisplayedRowCount(false))
                {
                    dataGridView.FirstDisplayedScrollingRowIndex = line;
                    for (int i = 0;
                         i < 8 && dataGridView.FirstDisplayedScrollingRowIndex > 0 &&
                    line < dataGridView.FirstDisplayedScrollingRowIndex + dataGridView.DisplayedRowCount(false);
                         ++i)
                    {
                        dataGridView.FirstDisplayedScrollingRowIndex = dataGridView.FirstDisplayedScrollingRowIndex - 1;
                    }
                    if (line >= dataGridView.FirstDisplayedScrollingRowIndex + dataGridView.DisplayedRowCount(false))
                    {
                        dataGridView.FirstDisplayedScrollingRowIndex = dataGridView.FirstDisplayedScrollingRowIndex + 1;
                    }
                }
                dataGridView.CurrentCell = dataGridView.Rows[line].Cells[0];
            }
            catch (Exception e)
            {
                // In rare situations there seems to be an invalid argument exceptions (or something like this). Concrete location isn't visible in stack
                // trace because use of Invoke(). So catch it, and log (better than crashing the app).
                Logger.logError(e.ToString());
            }
        }

        public void AddBookmarkOverlays()
        {
            const int OVERSCAN = 20;
            int firstLine = dataGridView.FirstDisplayedScrollingRowIndex;
            if (firstLine < 0)
            {
                return;
            }

            firstLine -= OVERSCAN;
            if (firstLine < 0)
            {
                firstLine = 0;
            }

            int oversizeCount = OVERSCAN;

            for (int i = firstLine; i < dataGridView.RowCount; ++i)
            {
                if (!dataGridView.Rows[i].Displayed && i > dataGridView.FirstDisplayedScrollingRowIndex)
                {
                    if (oversizeCount-- < 0)
                    {
                        break;
                    }
                }
                if (BookmarkProvider.IsBookmarkAtLine(i))
                {
                    Bookmark bookmark = BookmarkProvider.GetBookmarkForLine(i);
                    if (bookmark.Text.Length > 0)
                    {
                        BookmarkOverlay overlay = bookmark.Overlay;
                        overlay.Bookmark = bookmark;

                        Rectangle r;
                        if (dataGridView.Rows[i].Displayed)
                        {
                            r = dataGridView.GetCellDisplayRectangle(0, i, false);
                        }
                        else
                        {
                            r = dataGridView.GetCellDisplayRectangle(0, dataGridView.FirstDisplayedScrollingRowIndex, false);
                            int heightSum = 0;
                            if (dataGridView.FirstDisplayedScrollingRowIndex < i)
                            {
                                for (int rn = dataGridView.FirstDisplayedScrollingRowIndex + 1; rn < i; ++rn)
                                {
                                    heightSum += GetRowHeight(rn);
                                }
                                r.Offset(0, r.Height + heightSum);
                            }
                            else
                            {
                                for (int rn = dataGridView.FirstDisplayedScrollingRowIndex + 1; rn > i; --rn)
                                {
                                    heightSum += GetRowHeight(rn);
                                }
                                r.Offset(0, -(r.Height + heightSum));
                            }
                        }
                        if (Logger.IsDebug)
                        {
                            Logger.logDebug("AddBookmarkOverlay() r.Location=" + r.Location.X + ", width=" + r.Width + ", scroll_offset=" + dataGridView.HorizontalScrollingOffset);
                        }
                        overlay.Position = r.Location - new Size(dataGridView.HorizontalScrollingOffset, 0);
                        overlay.Position = overlay.Position + new Size(10, r.Height / 2);
                        dataGridView.AddOverlay(overlay);
                    }
                }
            }
        }

        public bool ShowBookmarkBubbles
        {
            get
            {
                return _guiStateArgs.ShowBookmarkBubbles;
            }
            set
            {
                _guiStateArgs.ShowBookmarkBubbles = dataGridView.PaintWithOverlays = value;
                dataGridView.Refresh();
            }
        }

        public void ToggleBookmark()
        {
            DataGridView gridView;
            int lineNum;

            if (filterGridView.Focused)
            {
                gridView = filterGridView;
                if (gridView.CurrentCellAddress == null || gridView.CurrentCellAddress.Y == -1)
                {
                    return;
                }
                lineNum = _filterResultList[gridView.CurrentCellAddress.Y];
            }
            else
            {
                gridView = dataGridView;
                if (gridView.CurrentCellAddress == null || gridView.CurrentCellAddress.Y == -1)
                {
                    return;
                }
                lineNum = dataGridView.CurrentCellAddress.Y;
            }

            ToggleBookmark(lineNum);
        }

        public void ToggleBookmark(int lineNum)
        {
            if (BookmarkProvider.IsBookmarkAtLine(lineNum))
            {
                Bookmark bookmark = BookmarkProvider.GetBookmarkForLine(lineNum);
                if (bookmark.Text != null && bookmark.Text.Length > 0)
                {
                    if (DialogResult.No == MessageBox.Show("There's a comment attached to the bookmark. Really remove the bookmark?", "LogExpert", MessageBoxButtons.YesNo))
                    {
                        return;
                    }
                }
                BookmarkProvider.RemoveBookmarkForLine(lineNum);
            }
            else
            {
                BookmarkProvider.AddBookmark(new Bookmark(lineNum));
            }
            dataGridView.Refresh();
            filterGridView.Refresh();
        }

        public void SetBookmarkFromTrigger(int lineNum, string comment)
        {
            lock (_bookmarkLock)
            {
                string line = CurrentLogFileReader.GetLogLine(lineNum);
                if (line == null)
                {
                    return;
                }
                ParamParser paramParser = new ParamParser(comment);
                try
                {
                    comment = paramParser.ReplaceParams(line, lineNum, FileName);
                }
                catch (ArgumentException)
                {
                    // occurs on invalid regex
                }
                if (BookmarkProvider.IsBookmarkAtLine(lineNum))
                {
                    BookmarkProvider.RemoveBookmarkForLine(lineNum);
                }
                BookmarkProvider.AddBookmark(new Bookmark(lineNum, comment));
            }
        }

        public void JumpToNextBookmark(bool isForward)
        {
            int currentBookMarkCount = BookmarkProvider.Bookmarks.Count;
            if (currentBookMarkCount > 0)
            {
                int bookmarkIndex = 0;

                bookmarkIndex = FindNextBookmarkIndex(dataGridView.CurrentCellAddress.Y, isForward);

                bookmarkIndex = currentBookMarkCount.SanitizeIndex(bookmarkIndex);

                if (filterGridView.Focused)
                {
                    int startIndex = bookmarkIndex;
                    bool wrapped = false;

                    //Search for a bookmarked and visible line
                    while (true)
                    {
                        int bookMarkedLine = BookmarkProvider.Bookmarks[bookmarkIndex].LineNum;
                        if (_filterResultList.Contains(bookMarkedLine))
                        {
                            //Bookmarked Line is in the filtered list display it
                            int filterLine = _filterResultList.IndexOf(bookMarkedLine);
                            filterGridView.Rows[filterLine].Selected = true;
                            filterGridView.CurrentCell = filterGridView.Rows[filterLine].Cells[0];
                            break;
                        }

                        //Bookmarked line is not visible with the current filter, search for another
                        bookmarkIndex = currentBookMarkCount.GetNextIndex(bookmarkIndex, isForward, out wrapped);

                        if (wrapped &&
                            ((isForward && bookmarkIndex >= startIndex) ||
                            (!isForward && bookmarkIndex <= startIndex)))
                        {
                            //We checked already this index, break out of the loop
                            break;
                        }
                    }
                }
                else
                {
                    int lineNum = BookmarkProvider.Bookmarks[bookmarkIndex].LineNum;
                    SelectLine(lineNum, false);
                }
            }
        }

        public void DeleteBookmarks(List<int> lineNumList)
        {
            bool bookmarksPresent = false;
            foreach (int lineNum in lineNumList)
            {
                if (lineNum != -1)
                {
                    if (BookmarkProvider.IsBookmarkAtLine(lineNum) && BookmarkProvider.GetBookmarkForLine(lineNum).Text.Length > 0)
                    {
                        bookmarksPresent = true;
                        break;
                    }
                }
            }
            if (bookmarksPresent)
            {
                if (MessageBox.Show("There are some comments in the bookmarks. Really remove bookmarks?", "LogExpert", MessageBoxButtons.YesNo) == DialogResult.No)
                {
                    return;
                }
            }
            BookmarkProvider.RemoveBookmarksForLines(lineNumList);
        }

        public void LogWindowActivated()
        {
            if (_guiStateArgs.FollowTail && !_isDeadFile)
            {
                OnTailFollowed(new EventArgs());
            }
            if (Preferences.timestampControl)
            {
                SetTimestampLimits();
                SyncTimestampDisplay();
            }
            dataGridView.Focus();

            SendGuiStateUpdate();
            SendStatusLineUpdate();
            SendProgressBarUpdate();
        }

        public void SetCellSelectionMode(bool isCellMode)
        {
            if (isCellMode)
            {
                dataGridView.SelectionMode = DataGridViewSelectionMode.CellSelect;
            }
            else
            {
                dataGridView.SelectionMode = DataGridViewSelectionMode.FullRowSelect;
            }
            _guiStateArgs.CellSelectMode = isCellMode;
        }

        public void TimeshiftEnabled(bool isEnabled, string shiftValue)
        {
            _guiStateArgs.TimeshiftEnabled = isEnabled;
            SetTimestampLimits();
            SetTimeshiftValue(shiftValue);
        }

        public void SetTimeshiftValue(string value)
        {
            _guiStateArgs.TimeshiftText = value;
            if (CurrentColumnizer.IsTimeshiftImplemented())
            {
                try
                {
                    if (_guiStateArgs.TimeshiftEnabled)
                    {
                        try
                        {
                            string text = _guiStateArgs.TimeshiftText;
                            if (text.StartsWith("+"))
                            {
                                text = text.Substring(1);
                            }
                            TimeSpan timeSpan = TimeSpan.Parse(text);
                            int diff = (int)(timeSpan.Ticks / TimeSpan.TicksPerMillisecond);
                            CurrentColumnizer.SetTimeOffset(diff);
                        }
                        catch (Exception)
                        {
                            CurrentColumnizer.SetTimeOffset(0);
                        }
                    }
                    else
                        CurrentColumnizer.SetTimeOffset(0);
                    dataGridView.Refresh();
                    filterGridView.Refresh();
                    if (CurrentColumnizer.IsTimeshiftImplemented())
                    {
                        SetTimestampLimits();
                        SyncTimestampDisplay();
                    }
                }
                catch (FormatException ex)
                {
                    Logger.logError(ex.StackTrace);
                }
            }
        }

        public void CopyMarkedLinesToTab()
        {
            if (dataGridView.SelectionMode == DataGridViewSelectionMode.FullRowSelect)
            {
                List<int> lineNumList = new List<int>();
                foreach (DataGridViewRow row in dataGridView.SelectedRows)
                {
                    if (row.Index != -1)
                    {
                        lineNumList.Add(row.Index);
                    }
                }
                lineNumList.Sort();
                // create dummy FilterPipe for connecting line numbers to original window
                // setting IsStopped to true prevents further filter processing
                FilterPipe pipe = new FilterPipe(new FilterParams(), this);
                pipe.IsStopped = true;
                WritePipeToTab(pipe, lineNumList, Text + "->C", null);
            }
            else
            {
                string fileName = Path.GetTempFileName();
                FileStream fStream = new FileStream(fileName, FileMode.Append, FileAccess.Write, FileShare.Read);
                StreamWriter writer = new StreamWriter(fStream, Encoding.Unicode);

                DataObject data = dataGridView.GetClipboardContent();
                string text = data.GetText(TextDataFormat.Text);
                writer.Write(text);

                writer.Close();
                string title = Util.GetNameFromPath(FileName) + "->Clip";
                _parentLogTabWin.AddTempFileTab(fileName, title);
            }
        }

        /// <summary>
        /// Change the file encoding. May force a reload if byte count ot preamble lenght differs from previous used encoding.
        /// </summary>
        /// <param name="encoding"></param>
        public void ChangeEncoding(Encoding encoding)
        {
            CurrentLogFileReader.ChangeEncoding(encoding);
            EncodingOptions.Encoding = encoding;
            if (_guiStateArgs.CurrentEncoding.IsSingleByte != encoding.IsSingleByte ||
                _guiStateArgs.CurrentEncoding.GetPreamble().Length != encoding.GetPreamble().Length)
            {
                Reload();
            }
            else
            {
                dataGridView.Refresh();
                SendGuiStateUpdate();
            }
            _guiStateArgs.CurrentEncoding = CurrentLogFileReader.CurrentEncoding;
        }

        public void Reload()
        {
            SavePersistenceData(false);

            _reloadMemento = new ReloadMemento();
            _reloadMemento.currentLine = dataGridView.CurrentCellAddress.Y;
            _reloadMemento.firstDisplayedLine = dataGridView.FirstDisplayedScrollingRowIndex;
            _forcedColumnizerForLoading = CurrentColumnizer;

            if (_fileNames == null || !IsMultiFile)
            {
                LoadFile(FileName, EncodingOptions);
            }
            else
            {
                LoadFilesAsMulti(_fileNames, EncodingOptions);
            }
        }

        public void PreferencesChanged(Preferences newPreferences, bool isLoadTime, SettingsFlags flags)
        {
            if ((flags & SettingsFlags.GuiOrColors) == SettingsFlags.GuiOrColors)
            {
                _normalFont = new Font(new FontFamily(newPreferences.fontName), newPreferences.fontSize);
                _fontBold = new Font(NormalFont, FontStyle.Bold);
                _fontMonospaced = new Font("Courier New", Preferences.fontSize, FontStyle.Bold);

                dataGridView.DefaultCellStyle.Font = NormalFont;
                filterGridView.DefaultCellStyle.Font = NormalFont;
                _lineHeight = NormalFont.Height + 4;
                dataGridView.RowTemplate.Height = NormalFont.Height + 4;

                ShowBookmarkBubbles = Preferences.showBubbles;

                ApplyDataGridViewPrefs(dataGridView, newPreferences);
                ApplyDataGridViewPrefs(filterGridView, newPreferences);

                if (Preferences.timestampControl)
                {
                    SetTimestampLimits();
                    SyncTimestampDisplay();
                }
                if (isLoadTime)
                {
                    filterTailCheckBox.Checked = Preferences.filterTail;
                    syncFilterCheckBox.Checked = Preferences.filterSync;
                }

                _timeSpreadCalc.TimeMode = Preferences.timeSpreadTimeMode;
                timeSpreadingControl1.ForeColor = Preferences.timeSpreadColor;
                timeSpreadingControl1.ReverseAlpha = Preferences.reverseAlpha;
                if (CurrentColumnizer.IsTimeshiftImplemented())
                {
                    timeSpreadingControl1.Invoke(new MethodInvoker(timeSpreadingControl1.Refresh));
                    ShowTimeSpread(Preferences.showTimeSpread);
                }
                ToggleColumnFinder(Preferences.showColumnFinder, false);
            }

            if ((flags & SettingsFlags.FilterList) == SettingsFlags.FilterList)
            {
                HandleChangedFilterList();
            }

            if ((flags & SettingsFlags.FilterHistory) == SettingsFlags.FilterHistory)
            {
                UpdateFilterHistoryFromSettings();
            }
        }

        public bool ScrollToTimestamp(DateTime timestamp, bool roundToSeconds, bool triggerSyncCall)
        {
            if (InvokeRequired)
            {
                BeginInvoke(new Func<DateTime, bool, bool, bool>(ScrollToTimestampWorker), new object[] { timestamp, roundToSeconds, triggerSyncCall });
                return true;
            }
            else
            {
                return ScrollToTimestampWorker(timestamp, roundToSeconds, triggerSyncCall);
            }
        }

        public bool ScrollToTimestampWorker(DateTime timestamp, bool roundToSeconds, bool triggerSyncCall)
        {
            bool hasScrolled = false;
            if (!CurrentColumnizer.IsTimeshiftImplemented() || dataGridView.RowCount == 0)
            {
                return false;
            }

            int currentLine = dataGridView.CurrentCellAddress.Y;
            if (currentLine < 0 || currentLine >= dataGridView.RowCount)
            {
                currentLine = 0;
            }
            int foundLine = FindTimestampLine(currentLine, timestamp, roundToSeconds);
            if (foundLine >= 0)
            {
                SelectAndEnsureVisible(foundLine, triggerSyncCall);
                hasScrolled = true;
            }
            return hasScrolled;
        }

        public int FindTimestampLine(int lineNum, DateTime timestamp, bool roundToSeconds)
        {
            int foundLine = FindTimestampLine_Internal(lineNum, 0, dataGridView.RowCount - 1, timestamp, roundToSeconds);
            if (foundLine >= 0)
            {
                // go backwards to the first occurence of the hit
                DateTime foundTimestamp = GetTimestampForLine(ref foundLine, roundToSeconds);
                while (foundTimestamp.CompareTo(timestamp) == 0 && foundLine >= 0)
                {
                    foundLine--;
                    foundTimestamp = GetTimestampForLine(ref foundLine, roundToSeconds);
                }
                if (foundLine < 0)
                {
                    return 0;
                }
                else
                {
                    foundLine++;
                    GetTimestampForLineForward(ref foundLine, roundToSeconds); // fwd to next valid timestamp
                    return foundLine;
                }
            }
            return -foundLine;
        }

        public int FindTimestampLine_Internal(int lineNum, int rangeStart, int rangeEnd, DateTime timestamp, bool roundToSeconds)
        {
            Logger.logDebug("FindTimestampLine_Internal(): timestamp=" + timestamp + ", lineNum=" + lineNum + ", rangeStart=" + rangeStart + ", rangeEnd=" + rangeEnd);
            int refLine = lineNum;
            DateTime currentTimestamp = GetTimestampForLine(ref refLine, roundToSeconds);
            if (currentTimestamp.CompareTo(timestamp) == 0)
            {
                return lineNum;
            }
            if (timestamp < currentTimestamp)
            {
                rangeEnd = lineNum;
            }
            else
            {
                rangeStart = lineNum;
            }

            if (rangeEnd - rangeStart <= 0)
            {
                return -lineNum;
            }

            lineNum = (rangeEnd - rangeStart) / 2 + rangeStart;
            // prevent endless loop
            if (rangeEnd - rangeStart < 2)
            {
                currentTimestamp = GetTimestampForLine(ref rangeStart, roundToSeconds);
                if (currentTimestamp.CompareTo(timestamp) == 0)
                {
                    return rangeStart;
                }
                currentTimestamp = GetTimestampForLine(ref rangeEnd, roundToSeconds);
                if (currentTimestamp.CompareTo(timestamp) == 0)
                {
                    return rangeEnd;
                }
                return -lineNum;
            }

            return FindTimestampLine_Internal(lineNum, rangeStart, rangeEnd, timestamp, roundToSeconds);
        }

        /**
         * Get the timestamp for the given line number. If the line
         * has no timestamp, the previous line will be checked until a
         * timestamp is found.
         */
        public DateTime GetTimestampForLine(ref int lineNum, bool roundToSeconds)
        {
            lock (_currentColumnizerLock)
            {
                if (!CurrentColumnizer.IsTimeshiftImplemented())
                {
                    return DateTime.MinValue;
                }
                Logger.logDebug("GetTimestampForLine(" + lineNum + ") enter");
                DateTime timeStamp = DateTime.MinValue;
                bool lookBack = false;
                if (lineNum >= 0 && lineNum < dataGridView.RowCount)
                {
                    while (timeStamp.CompareTo(DateTime.MinValue) == 0 && lineNum >= 0)
                    {
                        if (_isTimestampDisplaySyncing && _shouldTimestampDisplaySyncingCancel)
                        {
                            return DateTime.MinValue;
                        }
                        lookBack = true;
                        string logLine = CurrentLogFileReader.GetLogLine(lineNum);
                        if (logLine == null)
                        {
                            return DateTime.MinValue;
                        }
                        ColumnizerCallbackObject.LineNum = lineNum;
                        timeStamp = CurrentColumnizer.GetTimestamp(ColumnizerCallbackObject, logLine);
                        if (roundToSeconds)
                        {
                            timeStamp = timeStamp.Subtract(TimeSpan.FromMilliseconds(timeStamp.Millisecond));
                        }
                        lineNum--;
                    }
                }
                if (lookBack)
                    lineNum++;
                Logger.logDebug("GetTimestampForLine() leave with lineNum=" + lineNum);
                return timeStamp;
            }
        }

        /**
         * Get the timestamp for the given line number. If the line
         * has no timestamp, the next line will be checked until a
         * timestamp is found.
         */
        public DateTime GetTimestampForLineForward(ref int lineNum, bool roundToSeconds)
        {
            lock (_currentColumnizerLock)
            {
                if (!CurrentColumnizer.IsTimeshiftImplemented())
                {
                    return DateTime.MinValue;
                }

                DateTime timeStamp = DateTime.MinValue;
                bool lookFwd = false;
                if (lineNum >= 0 && lineNum < dataGridView.RowCount)
                {
                    while (timeStamp.CompareTo(DateTime.MinValue) == 0 && lineNum < dataGridView.RowCount)
                    {
                        lookFwd = true;
                        string logLine = CurrentLogFileReader.GetLogLine(lineNum);
                        if (logLine == null)
                        {
                            timeStamp = DateTime.MinValue;
                            break;
                        }
                        timeStamp = CurrentColumnizer.GetTimestamp(ColumnizerCallbackObject, logLine);
                        if (roundToSeconds)
                        {
                            timeStamp = timeStamp.Subtract(TimeSpan.FromMilliseconds(timeStamp.Millisecond));
                        }
                        lineNum++;
                    }
                }
                if (lookFwd)
                {
                    lineNum--;
                }
                return timeStamp;
            }
        }

        public void AppFocusLost()
        {
            InvalidateCurrentRow(dataGridView);
        }

        public void AppFocusGained()
        {
            InvalidateCurrentRow(dataGridView);
        }

        public string GetCurrentLine()
        {
            if (dataGridView.CurrentRow != null && dataGridView.CurrentRow.Index != -1)
            {
                return CurrentLogFileReader.GetLogLine(dataGridView.CurrentRow.Index);
            }
            return null;
        }

        public string GetLine(int lineNum)
        {
            if (lineNum < 0 || lineNum >= CurrentLogFileReader.LineCount)
            {
                return null;
            }
            return CurrentLogFileReader.GetLogLine(lineNum);
        }

        public int GetCurrentLineNum()
        {
            if (dataGridView.CurrentRow == null)
            {
                return -1;
            }
            return dataGridView.CurrentRow.Index;
        }

        public int GetRealLineNum()
        {
            int lineNum = GetCurrentLineNum();
            if (lineNum == -1)
            {
                return -1;
            }
            return CurrentLogFileReader.GetRealLineNumForVirtualLineNum(lineNum);
        }

        public string GetCurrentFileName()
        {
            if (dataGridView.CurrentRow != null && dataGridView.CurrentRow.Index != -1)
            {
                return CurrentLogFileReader.GetLogFileNameForLine(dataGridView.CurrentRow.Index);
            }
            return null;
        }

        public ILogFileInfo GetCurrentFileInfo()
        {
            if (dataGridView.CurrentRow != null && dataGridView.CurrentRow.Index != -1)
            {
                return CurrentLogFileReader.GetLogFileInfoForLine(dataGridView.CurrentRow.Index);
            }
            return null;
        }

        /// <summary>
        /// zero-based
        /// </summary>
        /// <param name="lineNum"></param>
        /// <returns></returns>
        public string GetCurrentFileName(int lineNum)
        {
            return CurrentLogFileReader.GetLogFileNameForLine(lineNum);
        }

        public void ShowLineColumn(bool show)
        {
            dataGridView.Columns[1].Visible = show;
            filterGridView.Columns[1].Visible = show;
        }

        public void PatternStatistic()
        {
            InitPatternWindow();
        }

        public void PatternStatisticSelectRange(PatternArgs patternArgs)
        {
            if (dataGridView.SelectionMode == DataGridViewSelectionMode.FullRowSelect)
            {
                List<int> lineNumList = new List<int>();
                foreach (DataGridViewRow row in dataGridView.SelectedRows)
                {
                    if (row.Index != -1)
                    {
                        lineNumList.Add(row.Index);
                    }
                }
                lineNumList.Sort();
                patternArgs.startLine = lineNumList[0];
                patternArgs.endLine = lineNumList[lineNumList.Count - 1];
            }
            else
            {
                if (dataGridView.CurrentCellAddress.Y != -1)
                {
                    patternArgs.startLine = dataGridView.CurrentCellAddress.Y;
                }
                else
                {
                    patternArgs.startLine = 0;
                }
                patternArgs.endLine = dataGridView.RowCount - 1;
            }
        }

        public void PatternStatistic(PatternArgs patternArgs)
        {
            Action<PatternArgs, Interfaces.ILogWindowSearch> fx = new Action<PatternArgs, Interfaces.ILogWindowSearch>(_fuzzyBlockDetection.TestStatistic);
            fx.BeginInvoke(patternArgs, this, null, null);
        }

        public void ExportBookmarkList()
        {
            SaveFileDialog dlg = new SaveFileDialog();
            dlg.Title = "Choose a file to save bookmarks into";
            dlg.AddExtension = true;
            dlg.DefaultExt = "csv";
            dlg.Filter = "CSV file (*.csv)|*.csv|Bookmark file (*.bmk)|*.bmk";
            dlg.FilterIndex = 1;
            dlg.FileName = Path.GetFileNameWithoutExtension(FileName);
            if (dlg.ShowDialog() == DialogResult.OK)
            {
                try
                {
                    BookmarkProvider.ExportBookmarkList(FileName, dlg.FileName);
                }
                catch (IOException e)
                {
                    MessageBox.Show("Error while exporting bookmark list: " + e.Message, "LogExpert");
                }
            }
        }

        public void ImportBookmarkList()
        {
            OpenFileDialog dlg = new OpenFileDialog();
            dlg.Title = "Choose a file to load bookmarks from";
            dlg.AddExtension = true;
            dlg.DefaultExt = "csv";
            dlg.Filter = "CSV file (*.csv)|*.csv|Bookmark file (*.bmk)|*.bmk";
            dlg.FilterIndex = 1;
            dlg.FileName = Path.GetFileNameWithoutExtension(FileName);

            if (dlg.ShowDialog() == DialogResult.OK)
            {
                try
                {
                    BookmarkProvider.ImportBookmarkList(FileName, dlg.FileName);

                    dataGridView.Refresh();
                    filterGridView.Refresh();
                }
                catch (IOException e)
                {
                    MessageBox.Show("Error while importing bookmark list: " + e.Message, "LogExpert");
                }
            }
        }

        public bool IsAdvancedOptionActive()
        {
            return (rangeCheckBox.Checked ||
            fuzzyKnobControl.Value > 0 ||
            filterKnobControl1.Value > 0 ||
            filterKnobControl2.Value > 0 ||
            invertFilterCheckBox.Checked ||
            columnRestrictCheckBox.Checked);
        }

        public void HandleChangedFilterList()
        {
            Invoke(new MethodInvoker(HandleChangedFilterListWorker));
        }

        public void HandleChangedFilterListWorker()
        {
            int index = filterListBox.SelectedIndex;
            filterListBox.Items.Clear();
            foreach (FilterParams filterParam in ConfigManager.Settings.filterList)
            {
                filterListBox.Items.Add(filterParam);
            }
            filterListBox.Refresh();
            if (index >= 0 && index < filterListBox.Items.Count)
            {
                filterListBox.SelectedIndex = index;
            }
            filterOnLoadCheckBox.Checked = Preferences.isFilterOnLoad;
            hideFilterListOnLoadCheckBox.Checked = Preferences.isAutoHideFilterList;
        }

        public void SetCurrentHighlightGroup(string groupName)
        {
            _guiStateArgs.HighlightGroupName = groupName;
            lock (_currentHighlightGroupLock)
            {
                _currentHighlightGroup = _parentLogTabWin.FindHighlightGroup(groupName);
                if (_currentHighlightGroup == null)
                {
                    if (_parentLogTabWin.HilightGroupList.Count > 0)
                    {
                        _currentHighlightGroup = _parentLogTabWin.HilightGroupList[0];
                    }
                    else
                    {
                        _currentHighlightGroup = new HilightGroup();
                    }
                }
                _guiStateArgs.HighlightGroupName = _currentHighlightGroup.GroupName;
            }
            SendGuiStateUpdate();
            BeginInvoke(new MethodInvoker(RefreshAllGrids));
        }

        public void SwitchMultiFile(bool enabled)
        {
            IsMultiFile = enabled;
            Reload();
        }

        public void AddOtherWindowToTimesync(LogWindow other)
        {
            if (other.IsTimeSynced)
            {
                if (IsTimeSynced)
                {
                    other.FreeFromTimeSync();
                    AddSlaveToTimesync(other);
                }
                else
                {
                    AddToTimeSync(other);
                }
            }
            else
            {
                AddSlaveToTimesync(other);
            }
        }

        public void AddToTimeSync(LogWindow master)
        {
            Logger.logInfo("Syncing window for " + Util.GetNameFromPath(FileName) + " to " + Util.GetNameFromPath(master.FileName));
            lock (_timeSyncListLock)
            {
                if (IsTimeSynced && master.TimeSyncList != TimeSyncList)  // already synced but master has different sync list
                {
                    FreeFromTimeSync();
                }
                TimeSyncList = master.TimeSyncList;
                TimeSyncList.AddWindow(this);
                ScrollToTimestamp(TimeSyncList.CurrentTimestamp, false, false);
            }
            OnSyncModeChanged();
        }

        public void FreeFromTimeSync()
        {
            lock (_timeSyncListLock)
            {
                if (TimeSyncList != null)
                {
                    Logger.logInfo("De-Syncing window for " + Util.GetNameFromPath(FileName));
                    TimeSyncList.WindowRemoved -= TimeSyncList_WindowRemoved;
                    TimeSyncList.RemoveWindow(this);
                    TimeSyncList = null;
                }
            }
            OnSyncModeChanged();
        }

        public IBookmarkData BookmarkData
        {
            get
            {
                return BookmarkProvider;
            }
        }

        public void AddTempFileTab(string fileName, string title)
        {
            _parentLogTabWin.AddTempFileTab(fileName, title);
        }

        /// <summary>
        /// Used to create a new tab and pipe the given content into it.
        /// </summary>
        /// <param name="lineEntryList"></param>
        public void WritePipeTab(IList<LineEntry> lineEntryList, string title)
        {
            FilterPipe pipe = new FilterPipe(new FilterParams(), this);
            pipe.IsStopped = true;
            pipe.Closed += new FilterPipe.ClosedEventHandler(Pipe_Disconnected);
            pipe.OpenFile();
            foreach (LineEntry entry in lineEntryList)
            {
                pipe.WriteToPipe(entry.logLine, entry.lineNum);
            }
            pipe.CloseFile();
            Invoke(new Action<FilterPipe, string, PersistenceData>(WriteFilterToTabFinished), new object[] { pipe, title, null });
        }



        void LogWindow_Disposed(object sender, EventArgs e)
        {
            _waitingForClose = true;
            _parentLogTabWin.HighlightSettingsChanged -= Parent_HighlightSettingsChanged;
            if (CurrentLogFileReader != null)
            {
                CurrentLogFileReader.DeleteAllContent();
            }
            FreeFromTimeSync();
        }


        void LogFileReader_LoadingStarted(object sender, LoadFileEventArgs e)
        {
            Invoke(new Action<LoadFileEventArgs>(LoadingStarted), new object[] { e });
        }

        void LogFileReader_FinishedLoading(object sender, EventArgs e)
        {
            Logger.logInfo("Finished loading.");
            _isLoading = false;
            _isDeadFile = false;
            if (!_waitingForClose)
            {
                Invoke(new MethodInvoker(LoadingFinished));
                Invoke(new MethodInvoker(LoadPersistenceData));
                Invoke(new MethodInvoker(SetGuiAfterLoading));
                _loadingFinishedEvent.Set();
                _externaLoadingFinishedEvent.Set();
                _timeSpreadCalc.SetLineCount(CurrentLogFileReader.LineCount);

                if (_reloadMemento != null)
                {
                    Invoke(new Action<ReloadMemento>(PositionAfterReload), new object[] { _reloadMemento });
                }
                if (filterTailCheckBox.Checked)
                {
                    Logger.logInfo("Refreshing filter view because of reload.");
                    Invoke(new MethodInvoker(FilterSearch)); // call on proper thread
                }

                HandleChangedFilterList();
            }
            _reloadMemento = null;
        }

        void LogFileReader_FileNotFound(object sender, EventArgs e)
        {
            if (!IsDisposed && !Disposing)
            {
                Logger.logInfo("Handling file not found event.");
                _isDeadFile = true;
                BeginInvoke(new MethodInvoker(LogfileDead));
            }
        }

        void LogFileReader_Respawned(object sender, EventArgs e)
        {
            BeginInvoke(new MethodInvoker(LogfileRespawned));
        }

        /**
         * Event handler for the Load event from LogfileReader
         */
        void LogFileReader_LoadFile(object sender, LoadFileEventArgs e)
        {
            if (e.NewFile)
            {
                Logger.logInfo("File created anew.");

                // File was new created (e.g. rollover)
                _isDeadFile = false;
                UnRegisterLogFileReaderEvents();
                dataGridView.CurrentCellChanged -= new EventHandler(DataGridView_CurrentCellChanged);
                MethodInvoker invoker = new MethodInvoker(ReloadNewFile);
                BeginInvoke(invoker);
                Logger.logDebug("Reloading invoked.");
                return;
            }

            if (!_isLoading)
            {
                return;
            }
            Action<LoadFileEventArgs> callback = new Action<LoadFileEventArgs>(UpdateProgress);
            BeginInvoke(callback, new object[] { e });
        }


        void UpdateProgress(LoadFileEventArgs e)
        {
            try
            {
                if (e.ReadPos >= e.FileSize)
                {
                    //Logger.logWarn("UpdateProgress(): ReadPos (" + e.ReadPos + ") is greater than file size (" + e.FileSize + "). Aborting Update");
                    return;
                }

                _statusEventArgs.FileSize = e.ReadPos;
                _progressEventArgs.MaxValue = (int)e.FileSize;
                _progressEventArgs.Value = (int)e.ReadPos;
                SendProgressBarUpdate();
                SendStatusLineUpdate();
            }
            catch (Exception ex)
            {
                Logger.logError("UpdateProgress(): \n" + ex + "\n" + ex.StackTrace);
            }
        }

        void LoadingStarted(LoadFileEventArgs e)
        {
            try
            {
                _statusEventArgs.FileSize = e.ReadPos;
                _statusEventArgs.StatusText = "Loading " + Util.GetNameFromPath(e.FileName);
                _progressEventArgs.Visible = true;
                _progressEventArgs.MaxValue = (int)e.FileSize;
                _progressEventArgs.Value = (int)e.ReadPos;
                SendProgressBarUpdate();
                SendStatusLineUpdate();
            }
            catch (Exception ex)
            {
                Logger.logError("LoadingStarted(): " + ex + "\n" + ex.StackTrace);
            }
        }


        void DataGridView_ColumnDividerDoubleClick(object sender, DataGridViewColumnDividerDoubleClickEventArgs e)
        {
            e.Handled = true;
            AutoResizeColumns(dataGridView);
        }

        void DataGridView_CellValueNeeded(object sender, DataGridViewCellValueEventArgs e)
        {
            e.Value = GetCellValue(e.RowIndex, e.ColumnIndex);
        }

        void DataGridView_CellPainting(object sender, DataGridViewCellPaintingEventArgs e)
        {
            DataGridView gridView = (DataGridView)sender;
            PaintHelper.CellPainting(this, gridView, e.RowIndex, e);
        }

        void DataGridView_CellValuePushed(object sender, DataGridViewCellValueEventArgs e)
        {
            if (!CurrentColumnizer.IsTimeshiftImplemented())
            {
                return;
            }
            string line = CurrentLogFileReader.GetLogLine(e.RowIndex);
            int offset = CurrentColumnizer.GetTimeOffset();
            CurrentColumnizer.SetTimeOffset(0);
            ColumnizerCallbackObject.LineNum = e.RowIndex;
            string[] cols = CurrentColumnizer.SplitLine(ColumnizerCallbackObject, line);
            CurrentColumnizer.SetTimeOffset(offset);
            if (cols.Length <= e.ColumnIndex - 2)
            {
                return;
            }

            string oldValue = cols[e.ColumnIndex - 2];
            string newValue = (string)e.Value;
            CurrentColumnizer.PushValue(ColumnizerCallbackObject, e.ColumnIndex - 2, newValue, oldValue);
            dataGridView.Refresh();
            TimeSpan timeSpan = new TimeSpan(CurrentColumnizer.GetTimeOffset() * TimeSpan.TicksPerMillisecond);
            string span = timeSpan.ToString();
            int index = span.LastIndexOf('.');
            if (index > 0)
            {
                span = span.Substring(0, index + 4);
            }
            SetTimeshiftValue(span);
            SendGuiStateUpdate();
        }

        void DataGridView_RowHeightInfoNeeded(object sender, DataGridViewRowHeightInfoNeededEventArgs e)
        {
            e.Height = GetRowHeight(e.RowIndex);
        }

        void DataGridView_CurrentCellChanged(object sender, EventArgs e)
        {
            if (dataGridView.CurrentRow != null)
            {
                _statusEventArgs.CurrentLineNum = dataGridView.CurrentRow.Index + 1;
                SendStatusLineUpdate();
                if (syncFilterCheckBox.Checked)
                {
                    SyncFilterGridPos();
                }

                if (CurrentColumnizer.IsTimeshiftImplemented() && Preferences.timestampControl)
                {
                    SyncTimestampDisplay();
                }
            }
        }

        void DataGridView_CellEndEdit(object sender, DataGridViewCellEventArgs e)
        {
            StatusLineText("");
        }

        void DataGridView_Paint(object sender, PaintEventArgs e)
        {
            if (ShowBookmarkBubbles)
            {
                AddBookmarkOverlays();
            }
        }

        void DataGridView_Scroll(object sender, ScrollEventArgs e)
        {
            if (e.ScrollOrientation == ScrollOrientation.VerticalScroll)
            {
                if (dataGridView.DisplayedRowCount(false) +
                    dataGridView.FirstDisplayedScrollingRowIndex >=
                    dataGridView.RowCount)
                {
                    if (!_guiStateArgs.FollowTail)
                    {
                        FollowTailChanged(true, false);
                    }
                    OnTailFollowed(new EventArgs());
                }
                else
                {
                    if (_guiStateArgs.FollowTail)
                    {
                        FollowTailChanged(false, false);
                    }
                }
                SendGuiStateUpdate();
            }
        }

        void DataGridView_KeyDown(object sender, KeyEventArgs e)
        {
            if (e.KeyCode == Keys.Tab && e.Modifiers == Keys.None)
            {
                filterGridView.Focus();
                e.Handled = true;
            }
            if (e.KeyCode == Keys.Tab && e.Modifiers == Keys.Control)
            {
                //parentLogTabWin.SwitchTab(e.Shift);
            }
            _shouldCallTimeSync = true;
        }

        void DataGridView_PreviewKeyDown(object sender, PreviewKeyDownEventArgs e)
        {
            if ((e.KeyCode == Keys.Tab) && e.Control)
            {
                e.IsInputKey = true;
            }
        }

        void DataGridView_CellContentDoubleClick(object sender, DataGridViewCellEventArgs e)
        {
            if (dataGridView.CurrentCell != null)
            {
                dataGridView.BeginEdit(false);
            }
        }

        void DataGridView_InvalidateCurrentRow(object sender, EventArgs e)
        {
            InvalidateCurrentRow(dataGridView);
        }

        void DataGridView_Resize(object sender, EventArgs e)
        {
            if (CurrentLogFileReader != null && dataGridView.RowCount > 0 &&
                _guiStateArgs.FollowTail)
            {
                dataGridView.FirstDisplayedScrollingRowIndex = dataGridView.RowCount - 1;
            }
        }

        void DataGridView_SelectionChanged(object sender, EventArgs e)
        {
            UpdateSelectionDisplay();
        }

        void DataGridView_CellContextMenuStripNeeded(object sender, DataGridViewCellContextMenuStripNeededEventArgs e)
        {
            if (e.RowIndex > 0 && e.RowIndex < dataGridView.RowCount &&
                !dataGridView.Rows[e.RowIndex].Selected)
            {
                SelectLine(e.RowIndex, false);
            }
            if (e.ContextMenuStrip == columnContextMenuStrip)
            {
                _selectedCol = e.ColumnIndex;
            }
        }

        void DataGridView_CellClick(object sender, DataGridViewCellEventArgs e)
        {
            _shouldCallTimeSync = true;
        }

        void DataGridView_CellDoubleClick(object sender, DataGridViewCellEventArgs e)
        {
            if (e.ColumnIndex == 0)
            {
                ToggleBookmark();
            }
        }

        void DataGridView_OverlayDoubleClicked(object sender, OverlayEventArgs e)
        {
            BookmarkComment(e.BookmarkOverlay.Bookmark);
        }



        void FilterGridView_CellPainting(object sender, DataGridViewCellPaintingEventArgs e)
        {
            if (e.RowIndex < 0 || e.ColumnIndex < 0 || _filterResultList.Count <= e.RowIndex)
            {
                e.Handled = false;
                return;
            }

            int lineNum = _filterResultList[e.RowIndex];
            string line = CurrentLogFileReader.GetLogLineWithWait(lineNum);

            if (line != null)
            {
                DataGridView gridView = (DataGridView)sender;
                HilightEntry entry = FindFirstNoWordMatchHilightEntry(line);

                PaintHelper.CellPaintFilter(this, gridView, e, lineNum, line, entry);
            }
        }

        void FilterGridView_CellValueNeeded(object sender, DataGridViewCellValueEventArgs e)
        {
            if (e.RowIndex < 0 || e.ColumnIndex < 0 || _filterResultList.Count <= e.RowIndex)
            {
                e.Value = "";
                return;
            }

            int lineNum = _filterResultList[e.RowIndex];
            e.Value = GetCellValue(lineNum, e.ColumnIndex);
        }

        void FilterGridView_RowHeightInfoNeeded(object sender, DataGridViewRowHeightInfoNeededEventArgs e)
        {
            e.Height = _lineHeight;
        }

        void FilterGridView_ColumnDividerDoubleClick(object sender, DataGridViewColumnDividerDoubleClickEventArgs e)
        {
            e.Handled = true;
            Action<DataGridView> fx = AutoResizeColumns;
            BeginInvoke(fx, new object[] { filterGridView });
        }

        void FilterGridView_CellDoubleClick(object sender, DataGridViewCellEventArgs e)
        {
            if (e.ColumnIndex == 0)
            {
                ToggleBookmark();
                return;
            }

            if (filterGridView.CurrentRow != null && e.RowIndex >= 0)
            {
                int lineNum = _filterResultList[filterGridView.CurrentRow.Index];
                SelectAndEnsureVisible(lineNum, true);
            }
        }

        void FilterGridView_KeyDown(object sender, KeyEventArgs e)
        {
            if (e.KeyCode == Keys.Enter)
            {
                if (filterGridView.CurrentCellAddress.Y >= 0 && filterGridView.CurrentCellAddress.Y < _filterResultList.Count)
                {
                    int lineNum = _filterResultList[filterGridView.CurrentCellAddress.Y];
                    SelectLine(lineNum, false);
                    e.Handled = true;
                }
            }
            if (e.KeyCode == Keys.Tab && e.Modifiers == Keys.None)
            {
                dataGridView.Focus();
                e.Handled = true;
            }
        }

        void FilterGridView_InvalidateCurrentRow(object sender, EventArgs e)
        {
            InvalidateCurrentRow(filterGridView);
        }

        void FilterGridView_CellContextMenuStripNeeded(object sender, DataGridViewCellContextMenuStripNeededEventArgs e)
        {
            if (e.ContextMenuStrip == columnContextMenuStrip)
            {
                _selectedCol = e.ColumnIndex;
            }
        }



        void EditControl_UpdateEditColumnDisplay(object sender, KeyEventArgs e)
        {
            UpdateEditColumnDisplay((DataGridViewTextBoxEditingControl)sender);
        }

        void EditControl_KeyPress(object sender, KeyPressEventArgs e)
        {
            UpdateEditColumnDisplay((DataGridViewTextBoxEditingControl)sender);
        }

        void EditControl_Click(object sender, EventArgs e)
        {
            UpdateEditColumnDisplay((DataGridViewTextBoxEditingControl)sender);
        }


        void FilterSearchButton_Click(object sender, EventArgs e)
        {
            FilterSearch();
        }

        void FilterComboBox_KeyDown(object sender, KeyEventArgs e)
        {
            if (e.KeyCode == Keys.Enter)
            {
                FilterSearch();
            }
        }

        void RangeCheckBox_CheckedChanged(object sender, EventArgs e)
        {
            filterRangeComboBox.Enabled = rangeCheckBox.Checked;
            CheckForFilterDirty();
        }

        void SyncFilterCheckBox_CheckedChanged(object sender, EventArgs e)
        {
            if (syncFilterCheckBox.Checked)
            {
                SyncFilterGridPos();
            }
        }

        void SelectionChangedTrigger_Signal(object sender, EventArgs e)
        {
            Logger.logDebug("Selection changed trigger");
            int selCount = dataGridView.SelectedRows.Count;
            if (selCount > 1)
            {
                StatusLineText(selCount + " selected lines");
            }
            else
            {
                if (IsMultiFile)
                {
                    MethodInvoker invoker = new MethodInvoker(DisplayCurrentFileOnStatusline);
                    invoker.BeginInvoke(null, null);
                }
                else
                {
                    StatusLineText("");
                }
            }
        }

        void selectedDataGridView_SelectionChanged(Object sender, EventArgs e)
        {
            selectedDataGridView.ClearSelection();
        }

        public void ClearSelectedView()
        {
            UpdateSelectedViewColumns();
        }

        public void DataGridView_DoubleClick(object sender, EventArgs e)
        {
            OpenSelectedRowInVim();
        }

        public void DataGridView_NewSelectionChanged(object sender, EventArgs e)
        {
            if (dataGridView.SelectedRows.Count == 1)
            {
                UpdateSelectedViewColumns();

                var selectedRow = dataGridView.SelectedRows[0];
                var testRow = new List<string>();

                for (int i = 0; i < selectedDataGridView.ColumnCount; i++)
                {
                    testRow.Add(ProcessTextForSelectedView(selectedRow.Cells[i].Value.ToString()));
                }

                selectedDataGridView.Rows.Add(testRow.ToArray());
            }
        }

        public string ProcessTextForSelectedView(string value)
        {
            return value.Replace(@"/\", Environment.NewLine);
        }

        public void UpdateSelectedViewColumns()
        {
            selectedDataGridView.ColumnCount = dataGridView.ColumnCount;

            for (int i = 0; i < selectedDataGridView.ColumnCount; i++)
            {
                var column = selectedDataGridView.Columns[i];

                column.HeaderText = dataGridView.Columns[i].HeaderText;
                column.Name = dataGridView.Columns[i].Name;
            }

            while (selectedDataGridView.Rows.Count > 0)
            {
                selectedDataGridView.Rows.RemoveAt(0);
            }
        }

        void FilterKnobControl1_CheckForFilterDirty(object sender, EventArgs e)
        {
            CheckForFilterDirty();
        }

        void FilterToTabButton_Click(object sender, EventArgs e)
        {
            FilterToTab();
        }

        void Pipe_Disconnected(FilterPipe sender)
        {
            lock (_filterPipeList)
            {
                _filterPipeList.Remove(sender);
                if (_filterPipeList.Count == 0)
                {
                    // reset naming counter to 0 if no more open filter tabs for this source window
                    _filterPipeNameCounter = 0;
                }
            }
        }

        void AdvancedButton_Click(object sender, EventArgs e)
        {
            _showAdvanced = !_showAdvanced;
            ShowAdvancedFilterPanel(_showAdvanced);
        }

        void SetTimestampLimits()
        {
            if (!CurrentColumnizer.IsTimeshiftImplemented())
            {
                return;
            }

            int line = 0;
            _guiStateArgs.MinTimestamp = GetTimestampForLineForward(ref line, true);
            line = dataGridView.RowCount - 1;
            _guiStateArgs.MaxTimestamp = GetTimestampForLine(ref line, true);
            SendGuiStateUpdate();
        }

        void DataGridContextMenuStrip_Opening(object sender, CancelEventArgs e)
        {
            int lineNum = -1;
            if (dataGridView.CurrentRow != null)
            {
                lineNum = dataGridView.CurrentRow.Index;
            }
            if (lineNum == -1)
            {
                return;
            }
            int refLineNum = lineNum;

            copyToTabToolStripMenuItem.Enabled = dataGridView.SelectedCells.Count > 0;
            scrollAllTabsToTimestampToolStripMenuItem.Enabled = CurrentColumnizer.IsTimeshiftImplemented() &&
            GetTimestampForLine(ref refLineNum, false) != DateTime.MinValue;
            locateLineInOriginalFileToolStripMenuItem.Enabled = IsTempFile &&
            FilterPipe != null &&
            FilterPipe.GetOriginalLineNum(lineNum) != -1;
            markEditModeToolStripMenuItem.Enabled = !dataGridView.CurrentCell.ReadOnly;

            // Remove all "old" plugin entries
            int index = dataGridContextMenuStrip.Items.IndexOf(pluginSeparator);
            if (index > 0)
            {
                for (int i = index + 1; i < dataGridContextMenuStrip.Items.Count;)
                {
                    dataGridContextMenuStrip.Items.RemoveAt(i);
                }
            }

            // Add plugin entries
            bool isAdded = false;
            if (PluginRegistry.GetInstance().RegisteredContextMenuPlugins.Count > 0)
            {
                IList<int> lines = GetSelectedContent();
                foreach (IContextMenuEntry entry in PluginRegistry.GetInstance().RegisteredContextMenuPlugins)
                {
                    LogExpertCallback callback = new LogExpertCallback(this);
                    ContextMenuPluginEventArgs evArgs = new ContextMenuPluginEventArgs(entry, lines, CurrentColumnizer, callback);
                    EventHandler ev = new EventHandler(HandlePluginContextMenu);
                    string menuText = entry.GetMenuText(lines, CurrentColumnizer, callback);
                    if (menuText != null)
                    {
                        bool disabled = menuText.StartsWith("_");
                        if (disabled)
                        {
                            menuText = menuText.Substring(1);
                        }
                        ToolStripItem item = dataGridContextMenuStrip.Items.Add(menuText, null, ev);
                        item.Tag = evArgs;
                        item.Enabled = !disabled;
                        isAdded = true;
                    }
                }
            }
            pluginSeparator.Visible = isAdded;

            // enable/disable Temp Highlight item
            tempHighlightsToolStripMenuItem.Enabled = _tempHilightEntryList.Count > 0;

            markCurrentFilterRangeToolStripMenuItem.Enabled = filterRangeComboBox.Text != null && filterRangeComboBox.Text.Length > 0;

            if (CurrentColumnizer.IsTimeshiftImplemented())
            {
                IList<WindowFileEntry> list = _parentLogTabWin.GetListOfOpenFiles();
                syncTimestampsToToolStripMenuItem.Enabled = true;
                syncTimestampsToToolStripMenuItem.DropDownItems.Clear();
                EventHandler ev = new EventHandler(HandleSyncContextMenu);
                Font italicFont = new Font(syncTimestampsToToolStripMenuItem.Font.FontFamily, syncTimestampsToToolStripMenuItem.Font.Size, FontStyle.Italic);
                foreach (WindowFileEntry fileEntry in list)
                {
                    if (fileEntry.LogWindow != this)
                    {
                        ToolStripMenuItem item = syncTimestampsToToolStripMenuItem.DropDownItems.Add(fileEntry.Title, null, ev) as ToolStripMenuItem;
                        item.Tag = fileEntry;
                        item.Checked = TimeSyncList != null && TimeSyncList.Contains(fileEntry.LogWindow);
                        if (fileEntry.LogWindow.TimeSyncList != null && !fileEntry.LogWindow.TimeSyncList.Contains(this))
                        {
                            item.Font = italicFont;
                            item.ForeColor = Color.Blue;
                        }
                        item.Enabled = fileEntry.LogWindow.CurrentColumnizer.IsTimeshiftImplemented();
                    }
                }
            }
            else
            {
                syncTimestampsToToolStripMenuItem.Enabled = false;
            }
            freeThisWindowFromTimeSyncToolStripMenuItem.Enabled = TimeSyncList != null && TimeSyncList.Count > 1;
        }

        void Copy_Click(object sender, EventArgs e)
        {
            CopyMarkedLinesToClipboard();
        }

        void ScrollAllTabsToTimestampToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (CurrentColumnizer.IsTimeshiftImplemented())
            {
                int currentLine = dataGridView.CurrentCellAddress.Y;
                if (currentLine > 0 && currentLine < dataGridView.RowCount)
                {
                    int lineNum = currentLine;
                    DateTime timeStamp = GetTimestampForLine(ref lineNum, false);
                    if (timeStamp.Equals(DateTime.MinValue))  // means: invalid
                    {
                        return;
                    }
                    _parentLogTabWin.ScrollAllTabsToTimestamp(timeStamp, this);
                }
            }
        }

        void LocateLineInOriginalFileToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (dataGridView.CurrentRow != null && FilterPipe != null)
            {
                int lineNum = FilterPipe.GetOriginalLineNum(dataGridView.CurrentRow.Index);
                if (lineNum != -1)
                {
                    FilterPipe.LogWindow.SelectLine(lineNum, false);
                    _parentLogTabWin.SelectTab(FilterPipe.LogWindow);
                }
            }
        }

        void ToggleBoomarkToolStripMenuItem_Click(object sender, EventArgs e)
        {
            ToggleBookmark();
        }

        void MarkEditModeToolStripMenuItem_Click(object sender, EventArgs e)
        {
            StartEditMode();
        }

        void BookmarkWindow_BookmarkCommentChanged(object sender, EventArgs e)
        {
            dataGridView.Refresh();
        }

        void ColumnRestrictCheckBox_CheckedChanged(object sender, EventArgs e)
        {
            columnButton.Enabled = columnRestrictCheckBox.Checked;
            if (columnRestrictCheckBox.Checked) // disable when nothing to filter
            {
                columnNamesLabel.Visible = true;
                _filterParams.columnRestrict = true;
                columnNamesLabel.Text = CalculateColumnNames(_filterParams);
            }
            else
            {
                columnNamesLabel.Visible = false;
            }
            CheckForFilterDirty();
        }

        void ColumnButton_Click(object sender, EventArgs e)
        {
            _filterParams.currentColumnizer = _currentColumnizer;
            FilterColumnChooser chooser = new FilterColumnChooser(_filterParams);
            if (chooser.ShowDialog() == System.Windows.Forms.DialogResult.OK)
            {
                columnNamesLabel.Text = CalculateColumnNames(_filterParams);

                filterSearchButton.Image = _searchButtonImage;
                saveFilterButton.Enabled = false;
            }
        }

        void ColumnContextMenuStrip_Opening(object sender, CancelEventArgs e)
        {
            Control ctl = columnContextMenuStrip.SourceControl;
            DataGridView gridView = ctl as DataGridView;
            bool frozen = false;
            if (_freezeStateMap.ContainsKey(ctl))
            {
                frozen = _freezeStateMap[ctl];
            }
            freezeLeftColumnsUntilHereToolStripMenuItem.Checked = frozen;
            if (frozen)
            {
                freezeLeftColumnsUntilHereToolStripMenuItem.Text = "Frozen";
            }
            else
            {
                if (ctl is DataGridView)
                {
                    freezeLeftColumnsUntilHereToolStripMenuItem.Text = "Freeze left columns until here (" +
                    gridView.Columns[_selectedCol].HeaderText + ")";
                }
            }
            DataGridViewColumn col = gridView.Columns[_selectedCol];
            moveLeftToolStripMenuItem.Enabled = (col != null && col.DisplayIndex > 0);
            moveRightToolStripMenuItem.Enabled = (col != null && col.DisplayIndex < gridView.Columns.Count - 1);

            if (gridView.Columns.Count - 1 > _selectedCol)
            {
                DataGridViewColumn colRight = gridView.Columns.GetNextColumn(col, DataGridViewElementStates.None,
                                                  DataGridViewElementStates.None);
                moveRightToolStripMenuItem.Enabled = (colRight != null && colRight.Frozen == col.Frozen);
            }
            if (_selectedCol > 0)
            {
                DataGridViewColumn colLeft = gridView.Columns.GetPreviousColumn(col, DataGridViewElementStates.None,
                                                 DataGridViewElementStates.None);

                moveLeftToolStripMenuItem.Enabled = (colLeft != null && colLeft.Frozen == col.Frozen);
            }
            DataGridViewColumn colLast = gridView.Columns[gridView.Columns.Count - 1];
            moveToLastColumnToolStripMenuItem.Enabled = (colLast != null && colLast.Frozen == col.Frozen);

            // Fill context menu with column names
            //
            EventHandler ev = new EventHandler(HandleColumnItemContextMenu);
            allColumnsToolStripMenuItem.DropDownItems.Clear();
            foreach (DataGridViewColumn column in gridView.Columns)
            {
                if (column.HeaderText.Length > 0)
                {
                    ToolStripMenuItem item = allColumnsToolStripMenuItem.DropDownItems.Add(column.HeaderText, null, ev) as ToolStripMenuItem;
                    item.Tag = column;
                    item.Enabled = !column.Frozen;
                }
            }
        }

        void FreezeLeftColumnsUntilHereToolStripMenuItem_Click(object sender, EventArgs e)
        {
            Control ctl = columnContextMenuStrip.SourceControl;
            bool frozen = false;
            if (_freezeStateMap.ContainsKey(ctl))
            {
                frozen = _freezeStateMap[ctl];
            }
            frozen = !frozen;
            _freezeStateMap[ctl] = frozen;

            if (ctl is DataGridView)
            {
                DataGridView gridView = ctl as DataGridView;
                ApplyFrozenState(gridView);
            }
        }

        void MoveToLastColumnToolStripMenuItem_Click(object sender, EventArgs e)
        {
            DataGridView gridView = columnContextMenuStrip.SourceControl as DataGridView;
            DataGridViewColumn col = gridView.Columns[_selectedCol];
            if (col != null)
            {
                col.DisplayIndex = gridView.Columns.Count - 1;
            }
        }

        void MoveLeftToolStripMenuItem_Click(object sender, EventArgs e)
        {
            DataGridView gridView = columnContextMenuStrip.SourceControl as DataGridView;
            DataGridViewColumn col = gridView.Columns[_selectedCol];
            if (col != null && col.DisplayIndex > 0)
            {
                col.DisplayIndex = col.DisplayIndex - 1;
            }
        }

        void MoveRightToolStripMenuItem_Click(object sender, EventArgs e)
        {
            DataGridView gridView = columnContextMenuStrip.SourceControl as DataGridView;
            DataGridViewColumn col = gridView.Columns[_selectedCol];
            if (col != null && col.DisplayIndex < gridView.Columns.Count - 1)
            {
                col.DisplayIndex = col.DisplayIndex + 1;
            }
        }

        void HideColumnToolStripMenuItem_Click(object sender, EventArgs e)
        {
            DataGridView gridView = columnContextMenuStrip.SourceControl as DataGridView;
            DataGridViewColumn col = gridView.Columns[_selectedCol];
            col.Visible = false;
        }

        void RestoreColumnsToolStripMenuItem_Click(object sender, EventArgs e)
        {
            DataGridView gridView = columnContextMenuStrip.SourceControl as DataGridView;
            foreach (DataGridViewColumn col in gridView.Columns)
            {
                col.Visible = true;
            }
        }

        void TimeSpreadingControl1_LineSelected(object sender, SelectLineEventArgs e)
        {
            SelectLine(e.Line, false);
        }

        void SplitContainer1_SplitterMoved(object sender, SplitterEventArgs e)
        {
            advancedFilterSplitContainer.SplitterDistance = FILTER_ADCANCED_SPLITTER_DISTANCE;
        }

        void MarkFilterHitsInLogViewToolStripMenuItem_Click(object sender, EventArgs e)
        {
            SearchParams p = new SearchParams();
            p.searchText = _filterParams.searchText;
            p.isRegex = _filterParams.isRegex;
            p.isCaseSensitive = _filterParams.isCaseSensitive;
            AddSearchHitHighlightEntry(p);
        }

        void StatusLineTrigger_Signal(object sender, EventArgs e)
        {
            OnStatusLine(_statusEventArgs);
        }

        void ColumnComboBox_SelectionChangeCommitted(object sender, EventArgs e)
        {
            SelectColumn();
        }

        void ColumnComboBox_KeyDown(object sender, KeyEventArgs e)
        {
            if (e.KeyCode == Keys.Enter)
            {
                SelectColumn();
                dataGridView.Focus();
            }
        }

        void ColumnComboBox_PreviewKeyDown(object sender, PreviewKeyDownEventArgs e)
        {
            if (e.KeyCode == Keys.Down && e.Modifiers == Keys.Alt)
            {
                columnComboBox.DroppedDown = true;
            }
            if (e.KeyCode == Keys.Enter)
            {
                e.IsInputKey = true;
            }
        }

        void BookmarkProvider_BookmarkRemoved()
        {
            if (!_isLoading)
            {
                dataGridView.Refresh();
                filterGridView.Refresh();
            }
        }

        void BookmarkProvider_BookmarkAdded()
        {
            if (!_isLoading)
            {
                dataGridView.Refresh();
                filterGridView.Refresh();
            }
        }

        void BookmarkCommentToolStripMenuItem_Click(object sender, EventArgs e)
        {
            AddBookmarkAndEditComment();
        }

        void HighlightSelectionInLogFileToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (dataGridView.EditingControl is DataGridViewTextBoxEditingControl)
            {
                DataGridViewTextBoxEditingControl ctl =
                    dataGridView.EditingControl as DataGridViewTextBoxEditingControl;
                HilightEntry he = new HilightEntry(ctl.SelectedText, Color.Red, Color.Yellow,
                                      false, true, false, false, false, false, null, false);
                lock (_tempHilightEntryListLock)
                {
                    _tempHilightEntryList.Add(he);
                }
                dataGridView.CancelEdit();
                dataGridView.EndEdit();
                RefreshAllGrids();
            }
        }

        void CopyToolStripMenuItem1_Click(object sender, EventArgs e)
        {
            if (dataGridView.EditingControl is DataGridViewTextBoxEditingControl)
            {
                DataGridViewTextBoxEditingControl ctl =
                    dataGridView.EditingControl as DataGridViewTextBoxEditingControl;
                if (!string.IsNullOrEmpty(ctl.SelectedText))
                {
                    Clipboard.SetText(ctl.SelectedText);
                }
            }
        }

        void RemoveAllToolStripMenuItem_Click(object sender, EventArgs e)
        {
            RemoveTempHighlights();
        }

        void MakePermanentToolStripMenuItem_Click(object sender, EventArgs e)
        {
            lock (_tempHilightEntryListLock)
            {
                lock (_currentHighlightGroupLock)
                {
                    _currentHighlightGroup.HilightEntryList.AddRange(_tempHilightEntryList);
                    RemoveTempHighlights();
                    OnCurrentHighlightListChanged();
                }
            }
        }

        void MarkCurrentFilterRangeToolStripMenuItem_Click(object sender, EventArgs e)
        {
            MarkCurrentFilterRange();
        }

        void FilterForSelectionToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (dataGridView.EditingControl is DataGridViewTextBoxEditingControl)
            {
                DataGridViewTextBoxEditingControl ctl =
                    dataGridView.EditingControl as DataGridViewTextBoxEditingControl;
                splitContainer1.Panel2Collapsed = false;
                ResetFilterControls();
                FilterSearch(ctl.SelectedText);
            }
        }

        void SetSelectedTextAsBookmarkCommentToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (dataGridView.EditingControl is DataGridViewTextBoxEditingControl)
            {
                DataGridViewTextBoxEditingControl ctl =
                    dataGridView.EditingControl as DataGridViewTextBoxEditingControl;
                AddBookmarkComment(ctl.SelectedText);
            }
        }

        void FilterRegexCheckBox_MouseUp(object sender, MouseEventArgs e)
        {
            if (e.Button == MouseButtons.Right)
            {
                RegexHelperDialog dlg = new RegexHelperDialog();
                dlg.Owner = this;
                dlg.CaseSensitive = filterCaseSensitiveCheckBox.Checked;
                dlg.Pattern = filterComboBox.Text;
                DialogResult res = dlg.ShowDialog();
                if (res == DialogResult.OK)
                {
                    filterCaseSensitiveCheckBox.Checked = dlg.CaseSensitive;
                    filterComboBox.Text = dlg.Pattern;
                }
            }
        }

        // ================= Filter-Highlight stuff ===============================

        /// <summary>
        /// Event handler for the HighlightEvent generated by the HighlightThread
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        void HighlightThread_HighlightDoneEvent(object sender, HighlightEventArgs e)
        {
            BeginInvoke(new Action<HighlightEventArgs>(HighlightDoneEventWorker), new object[] { e });
        }

        /// <summary>
        /// Highlights the done event worker.
        /// </summary>
        /// <param name="e">The <see cref="LogExpert.HighlightEventArgs"/> instance containing the event data.</param>
        void HighlightDoneEventWorker(HighlightEventArgs e)
        {
            if (dataGridView.FirstDisplayedScrollingRowIndex > e.StartLine &&
                dataGridView.FirstDisplayedScrollingRowIndex < e.StartLine + e.Count ||
                dataGridView.FirstDisplayedScrollingRowIndex + dataGridView.DisplayedRowCount(true) >
                e.StartLine &&
                dataGridView.FirstDisplayedScrollingRowIndex + dataGridView.DisplayedRowCount(true) < e.StartLine + e.Count)
            {
                BeginInvoke(new MethodInvoker(RefreshAllGrids));
            }
        }

        void ToggleHighlightPanelButton_Click(object sender, EventArgs e)
        {
            ToggleHighlightPanel(highlightSplitContainer.Panel2Collapsed);
        }

        void SaveFilterButton_Click(object sender, EventArgs e)
        {
            FilterParams newParams = _filterParams.CreateCopy();
            newParams.color = Color.FromKnownColor(KnownColor.Black);
            ConfigManager.Settings.filterList.Add(newParams);
            OnFilterListChanged(this);
        }

        void DeleteFilterButton_Click(object sender, EventArgs e)
        {
            int index = filterListBox.SelectedIndex;
            if (index >= 0)
            {
                FilterParams filterParams = (FilterParams)filterListBox.Items[index];
                ConfigManager.Settings.filterList.Remove(filterParams);
                OnFilterListChanged(this);
                if (filterListBox.Items.Count > 0)
                {
                    filterListBox.SelectedIndex = filterListBox.Items.Count - 1;
                }
            }
        }

        void FilterUpButton_Click(object sender, EventArgs e)
        {
            int i = filterListBox.SelectedIndex;
            if (i > 0)
            {
                FilterParams filterParams = (FilterParams)filterListBox.Items[i];
                ConfigManager.Settings.filterList.RemoveAt(i);
                i--;
                ConfigManager.Settings.filterList.Insert(i, filterParams);
                OnFilterListChanged(this);
                filterListBox.SelectedIndex = i;
            }
        }

        void FilterDownButton_Click(object sender, EventArgs e)
        {
            int i = filterListBox.SelectedIndex;
            if (i < filterListBox.Items.Count - 1)
            {
                FilterParams filterParams = (FilterParams)filterListBox.Items[i];
                ConfigManager.Settings.filterList.RemoveAt(i);
                i++;
                ConfigManager.Settings.filterList.Insert(i, filterParams);
                OnFilterListChanged(this);
                filterListBox.SelectedIndex = i;
            }
        }

        void FilterListBox_MouseDoubleClick(object sender, MouseEventArgs e)
        {
            if (filterListBox.SelectedIndex >= 0)
            {
                FilterParams filterParams = (FilterParams)filterListBox.Items[filterListBox.SelectedIndex];
                FilterParams newParams = filterParams.CreateCopy();
                //newParams.historyList = ConfigManager.Settings.filterHistoryList;
                _filterParams = newParams;
                ReInitFilterParams(_filterParams);
                ApplyFilterParams();
                CheckForAdvancedButtonDirty();
                CheckForFilterDirty();
                filterSearchButton.Image = _searchButtonImage;
                saveFilterButton.Enabled = false;
                if (hideFilterListOnLoadCheckBox.Checked)
                {
                    ToggleHighlightPanel(false);
                }
                if (filterOnLoadCheckBox.Checked)
                {
                    FilterSearch();
                }
            }
        }

        void FilterListBox_DrawItem(object sender, DrawItemEventArgs e)
        {
            e.DrawBackground();
            if (e.Index >= 0)
            {
                FilterParams filterParams = (FilterParams)filterListBox.Items[e.Index];
                Rectangle rectangle = new Rectangle(0, e.Bounds.Top, e.Bounds.Width, e.Bounds.Height);

                Brush brush = ((e.State & DrawItemState.Selected) == DrawItemState.Selected) ? new SolidBrush(filterListBox.BackColor) : new SolidBrush(filterParams.color);

                e.Graphics.DrawString(filterParams.searchText, e.Font, brush,
                    new PointF(rectangle.Left, rectangle.Top));
                e.DrawFocusRectangle();
                brush.Dispose();
            }
        }

        // Color for filter list entry
        void ColorToolStripMenuItem_Click(object sender, EventArgs e)
        {
            int i = filterListBox.SelectedIndex;
            if (i < filterListBox.Items.Count && i >= 0)
            {
                FilterParams filterParams = (FilterParams)filterListBox.Items[i];
                ColorDialog dlg = new ColorDialog();
                dlg.CustomColors = new int[] { filterParams.color.ToArgb() };
                dlg.Color = filterParams.color;
                if (dlg.ShowDialog() == DialogResult.OK)
                {
                    filterParams.color = dlg.Color;
                    filterListBox.Refresh();
                }
            }
        }

        void FilterChanges_CheckForDirty(object sender, EventArgs e)
        {
            CheckForFilterDirty();
        }

        void FilterRegexCheckBox_CheckedChanged(object sender, EventArgs e)
        {
            fuzzyKnobControl.Enabled = !filterRegexCheckBox.Checked;
            fuzzyLabel.Enabled = !filterRegexCheckBox.Checked;
            CheckForFilterDirty();
        }

        void SetBookmarksOnSelectedLinesToolStripMenuItem_Click(object sender, EventArgs e)
        {
            SetBoomarksForSelectedFilterLines();
        }

        void Parent_HighlightSettingsChanged(object sender, EventArgs e)
        {
            string groupName = _guiStateArgs.HighlightGroupName;
            SetCurrentHighlightGroup(groupName);
        }

        void FilterOnLoadCheckBox_MouseClick(object sender, MouseEventArgs e)
        {
            HandleChangedFilterOnLoadSetting();
        }

        void FilterOnLoadCheckBox_KeyPress(object sender, KeyPressEventArgs e)
        {
            HandleChangedFilterOnLoadSetting();
        }

        void HideFilterListOnLoadCheckBox_MouseClick(object sender, MouseEventArgs e)
        {
            HandleChangedFilterOnLoadSetting();
        }

        void FilterToTabToolStripMenuItem_Click(object sender, EventArgs e)
        {
            FilterToTab();
        }

        void TimeSyncList_WindowRemoved(object sender, EventArgs e)
        {
            TimeSyncList syncList = sender as TimeSyncList;
            lock (_timeSyncListLock)
            {
                if (syncList.Count == 0 || syncList.Count == 1 && syncList.Contains(this))
                {
                    if (syncList == TimeSyncList)
                    {
                        TimeSyncList = null;
                        OnSyncModeChanged();
                    }
                }
            }
        }

        void FreeThisWindowFromTimeSyncToolStripMenuItem_Click(object sender, EventArgs e)
        {
            FreeFromTimeSync();
        }

        void LogWindow_InvalidateCurrentRow(object sender, EventArgs e)
        {
            InvalidateCurrentRow();
        }

        void HandlePluginContextMenu(object sender, EventArgs args)
        {
            if (sender is ToolStripItem)
            {
                ContextMenuPluginEventArgs menuArgs = (sender as ToolStripItem).Tag as ContextMenuPluginEventArgs;
                menuArgs.Entry.MenuSelected(menuArgs.LogLines, menuArgs.Columnizer, menuArgs.Callback);
            }
        }

        void HandleSyncContextMenu(object sender, EventArgs args)
        {
            if (sender is ToolStripItem)
            {
                WindowFileEntry entry = (sender as ToolStripItem).Tag as WindowFileEntry;

                if (TimeSyncList != null && TimeSyncList.Contains(entry.LogWindow))
                {
                    FreeSlaveFromTimesync(entry.LogWindow);
                }
                else
                {
                    AddOtherWindowToTimesync(entry.LogWindow);
                }
            }
        }

        void HandleColumnItemContextMenu(object sender, EventArgs args)
        {
            if (sender is ToolStripItem)
            {
                DataGridViewColumn column = ((sender as ToolStripItem).Tag as DataGridViewColumn);
                column.Visible = true;
                column.DataGridView.FirstDisplayedScrollingColumnIndex = column.Index;
            }
        }



        void SetColumnizer(ILogLineColumnizer columnizer)
        {
            int timeDiff = 0;
            if (CurrentColumnizer != null && CurrentColumnizer.IsTimeshiftImplemented())
            {
                timeDiff = CurrentColumnizer.GetTimeOffset();
            }

            SetColumnizerInternal(columnizer);

            if (CurrentColumnizer.IsTimeshiftImplemented())
            {
                CurrentColumnizer.SetTimeOffset(timeDiff);
            }
        }

        void StartProgressBar(int maxValue, string statusMessage)
        {
            if (this.InvokeRequired)
            {
                this.Invoke(new Action<int, string>(StartProgressBar), maxValue, statusMessage);
                return;
            }

            StatusLineText(statusMessage);

            _progressEventArgs.MinValue = 0;
            _progressEventArgs.MaxValue = maxValue;
            _progressEventArgs.Value = 0;
            _progressEventArgs.Visible = true;
            SendProgressBarUpdate();
        }

        void SetColumnizerInternal(ILogLineColumnizer columnizer)
        {
            Logger.logInfo("SetColumnizerInternal(): " + columnizer.GetName());

            ILogLineColumnizer oldColumnizer = CurrentColumnizer;
            bool oldColumnizerIsXmlType = CurrentColumnizer is ILogLineXmlColumnizer;
            bool oldColumnizerIsPreProcess = CurrentColumnizer is IPreProcessColumnizer;
            bool mustReload = false;

            // Check if the filtered columns disappeared, if so must refresh the UI
            if (_filterParams.columnRestrict)
            {
                string[] newColumns = columnizer != null ? columnizer.GetColumnNames() : new string[0];
                bool colChanged = false;
                if (dataGridView.ColumnCount - 2 == newColumns.Length) // two first columns are 'marker' and 'line number'
                {
                    for (int i = 0; i < newColumns.Length; i++)
                    {
                        if (dataGridView.Columns[i].HeaderText != newColumns[i])
                        {
                            colChanged = true;
                            break; // one change is sufficient
                        }
                    }
                }
                else
                {
                    colChanged = true;
                }

                if (colChanged)
                {
                    // Update UI
                    columnNamesLabel.Text = CalculateColumnNames(_filterParams);
                }
            }

            Type oldColType = _filterParams.currentColumnizer != null ? _filterParams.currentColumnizer.GetType() : null;
            Type newColType = columnizer != null ? columnizer.GetType() : null;
            if (oldColType != newColType && _filterParams.columnRestrict && _filterParams.isFilterTail)
            {
                _filterParams.columnList.Clear();
            }
            if (CurrentColumnizer == null || !CurrentColumnizer.GetType().Equals(columnizer.GetType()))
            {
                CurrentColumnizer = columnizer;
                _freezeStateMap.Clear();
                if (CurrentLogFileReader != null)
                {
                    IPreProcessColumnizer preprocessColumnizer = CurrentColumnizer as IPreProcessColumnizer;
                    if (preprocessColumnizer != null)
                    {
                        CurrentLogFileReader.PreProcessColumnizer = preprocessColumnizer;
                    }
                    else
                    {
                        CurrentLogFileReader.PreProcessColumnizer = null;
                    }
                }
                // always reload when choosing XML columnizers
                if (CurrentLogFileReader != null && CurrentColumnizer is ILogLineXmlColumnizer)
                {
                    //forcedColumnizer = currentColumnizer; // prevent Columnizer selection on SetGuiAfterReload()
                    mustReload = true;
                }
                // Reload when choosing no XML columnizer but previous columnizer was XML
                if (CurrentLogFileReader != null && !(CurrentColumnizer is ILogLineXmlColumnizer) && oldColumnizerIsXmlType)
                {
                    CurrentLogFileReader.IsXmlMode = false;
                    //forcedColumnizer = currentColumnizer; // prevent Columnizer selection on SetGuiAfterReload()
                    mustReload = true;
                }
                // Reload when previous columnizer was PreProcess and current is not, and vice versa.
                // When the current columnizer is a preProcess columnizer, reload in every case.
                bool isCurrentColumnizerIPreProcessColumnizer = CurrentColumnizer is IPreProcessColumnizer;
                if ((isCurrentColumnizerIPreProcessColumnizer != oldColumnizerIsPreProcess) ||
                    isCurrentColumnizerIPreProcessColumnizer)
                {
                    //forcedColumnizer = currentColumnizer; // prevent Columnizer selection on SetGuiAfterReload()
                    mustReload = true;
                }
            }
            else
            {
                CurrentColumnizer = columnizer;
            }

            IInitColumnizer initColumnizer = oldColumnizer as IInitColumnizer;

            if (initColumnizer != null)
            {
                initColumnizer.DeSelected(new ColumnizerCallback(this));
            }
            initColumnizer = columnizer as IInitColumnizer;
            if (initColumnizer != null)
            {
                initColumnizer.Selected(new ColumnizerCallback(this));
            }

            SetColumnizer(columnizer, dataGridView);
            SetColumnizer(columnizer, filterGridView);
            if (_patternWindow != null)
            {
                _patternWindow.SetColumnizer(columnizer);
            }

            _guiStateArgs.TimeshiftPossible = columnizer.IsTimeshiftImplemented();
            SendGuiStateUpdate();

            if (CurrentLogFileReader != null)
            {
                dataGridView.RowCount = CurrentLogFileReader.LineCount;
            }
            if (_filterResultList != null)
            {
                filterGridView.RowCount = _filterResultList.Count;
            }
            if (mustReload)
            {
                Reload();
            }
            else
            {
                if (CurrentColumnizer.IsTimeshiftImplemented())
                {
                    SetTimestampLimits();
                    SyncTimestampDisplay();
                }
                Settings settings = ConfigManager.Settings;
                ShowLineColumn(!settings.hideLineColumn);
                ShowTimeSpread(Preferences.showTimeSpread && columnizer.IsTimeshiftImplemented());
            }

            if (!columnizer.IsTimeshiftImplemented() && IsTimeSynced)
            {
                FreeFromTimeSync();
            }

            columnComboBox.Items.Clear();
            foreach (String columnName in columnizer.GetColumnNames())
            {
                columnComboBox.Items.Add(columnName);
            }
            columnComboBox.SelectedIndex = 0;

            OnColumnizerChanged(CurrentColumnizer);
        }

        protected void RegisterLogFileReaderEvents()
        {
            CurrentLogFileReader.LoadFile += LogFileReader_LoadFile;
            CurrentLogFileReader.LoadingFinished += LogFileReader_FinishedLoading;
            CurrentLogFileReader.LoadingStarted += LogFileReader_LoadingStarted;
            CurrentLogFileReader.FileNotFound += LogFileReader_FileNotFound;
            CurrentLogFileReader.Respawned += LogFileReader_Respawned;
            // FileSizeChanged is not registered here because it's registered after loading has finished
        }

        protected void UnRegisterLogFileReaderEvents()
        {
            if (CurrentLogFileReader != null)
            {
                CurrentLogFileReader.LoadFile -= LogFileReader_LoadFile;
                CurrentLogFileReader.LoadingFinished -= LogFileReader_FinishedLoading;
                CurrentLogFileReader.LoadingStarted -= LogFileReader_LoadingStarted;
                CurrentLogFileReader.FileNotFound -= LogFileReader_FileNotFound;
                CurrentLogFileReader.Respawned -= LogFileReader_Respawned;
                CurrentLogFileReader.FileSizeChanged -= FileSizeChangedHandler;
            }
        }

        protected void LoadPersistenceOptions(PersistenceData persistenceData)
        {
            splitContainer1.SplitterDistance = persistenceData.filterPosition;
            splitContainer1.Panel2Collapsed = !persistenceData.filterVisible;
            ToggleHighlightPanel(persistenceData.filterSaveListVisible);
            ShowAdvancedFilterPanel(persistenceData.filterAdvanced);
        }

        void SetDefaultsFromPrefs()
        {
            filterTailCheckBox.Checked = Preferences.filterTail;
            syncFilterCheckBox.Checked = Preferences.filterSync;
            FollowTailChanged(Preferences.followTail, false);
            _multifileOptions = ObjectClone.Clone<MultifileOptions>(Preferences.multifileOptions);
        }

        void LoadPersistenceData()
        {
            if (InvokeRequired)
            {
                Invoke(new MethodInvoker(LoadPersistenceData));
                return;
            }

            if (!Preferences.saveSessions && !ForcePersistenceLoading && ForcedPersistenceFileName == null)
            {
                SetDefaultsFromPrefs();
                return;
            }

            if (IsTempFile)
            {
                SetDefaultsFromPrefs();
                return;
            }

            ForcePersistenceLoading = false;  // force only 1 time (while session load)

            try
            {
                PersistenceData persistenceData;
                if (ForcedPersistenceFileName == null)
                {
                    persistenceData = Persister.LoadPersistenceData(FileName, Preferences);
                }
                else
                {
                    persistenceData = Persister.LoadPersistenceDataFromFixedFile(ForcedPersistenceFileName);
                }

                if (persistenceData.lineCount > CurrentLogFileReader.LineCount)
                {
                    // outdated persistence data (logfile rollover)
                    // MessageBox.Show(this, "Persistence data for " + FileName + " is outdated. It was discarded.", "Log Expert");
                    Logger.logInfo("Persistence data for " + FileName + " is outdated. It was discarded.");
                    LoadPersistenceOptions();
                    return;
                }
                BookmarkProvider.BookmarkList = persistenceData.bookmarkList;
                _rowHeightList = persistenceData.rowHeightList;
                try
                {
                    if (persistenceData.currentLine >= 0 && persistenceData.currentLine < dataGridView.RowCount)
                    {
                        SelectLine(persistenceData.currentLine, false);
                    }
                    else
                    {
                        if (CurrentLogFileReader.LineCount > 0)
                        {
                            dataGridView.FirstDisplayedScrollingRowIndex = CurrentLogFileReader.LineCount - 1;
                            SelectLine(CurrentLogFileReader.LineCount - 1, false);
                        }
                    }
                    if (persistenceData.firstDisplayedLine >= 0 && persistenceData.firstDisplayedLine < dataGridView.RowCount)
                    {
                        dataGridView.FirstDisplayedScrollingRowIndex = persistenceData.firstDisplayedLine;
                    }
                    if (persistenceData.followTail)
                    {
                        FollowTailChanged(persistenceData.followTail, false);
                    }
                }
                catch (ArgumentOutOfRangeException)
                {
                    // FirstDisplayedScrollingRowIndex errechnet manchmal falsche Scroll-Ranges???
                }

                if (Preferences.saveFilters)
                {
                    RestoreFilters(persistenceData);
                }
            }
            catch (IOException ex)
            {
                SetDefaultsFromPrefs();
                Logger.logError("Error loading bookmarks: " + ex.Message);
            }
        }

        void RestoreFilters(PersistenceData persistenceData)
        {
            if (persistenceData.filterParamsList.Count > 0)
            {
                _filterParams = persistenceData.filterParamsList[0];
                ReInitFilterParams(_filterParams);
            }
            ApplyFilterParams();  // re-loaded filter settingss
            BeginInvoke(new MethodInvoker(FilterSearch));
            try
            {
                splitContainer1.SplitterDistance = persistenceData.filterPosition;
                splitContainer1.Panel2Collapsed = !persistenceData.filterVisible;
            }
            catch (InvalidOperationException e)
            {
                Logger.logError("Error setting splitter distance: " + e.Message);
            }
            ShowAdvancedFilterPanel(persistenceData.filterAdvanced);
            if (_filterPipeList.Count == 0)     // don't restore if it's only a reload
            {
                RestoreFilterTabs(persistenceData);
            }
        }

        void RestoreFilterTabs(PersistenceData persistenceData)
        {
            foreach (FilterTabData data in persistenceData.filterTabDataList)
            {
                FilterParams persistFilterParams = data.filterParams;
                ReInitFilterParams(persistFilterParams);
                List<int> filterResultList = new List<int>();
                List<int> filterHitList = new List<int>();
                Filter(persistFilterParams, filterResultList, _lastFilterLinesList, filterHitList);
                FilterPipe pipe = new FilterPipe(persistFilterParams.CreateCopy(), this);
                WritePipeToTab(pipe, filterResultList, data.persistenceData.tabName, data.persistenceData);
            }
        }

        void ReInitFilterParams(FilterParams filterParams)
        {
            filterParams.searchText = filterParams.searchText;   // init "lowerSearchText"
            filterParams.rangeSearchText = filterParams.rangeSearchText;   // init "lowerRangesearchText"
            filterParams.currentColumnizer = CurrentColumnizer;
            if (filterParams.isRegex)
            {
                try
                {
                    filterParams.CreateRegex();
                }
                catch (ArgumentException)
                {
                    StatusLineError("Invalid regular expression");
                    return;
                }
            }
        }

        protected void EnterLoadFileStatus()
        {
            EnterLoadFileStatusBase();

            dataGridView.ClearSelection();
            dataGridView.RowCount = 0;
        }

        void PositionAfterReload(ReloadMemento reloadMemento)
        {
            if (_reloadMemento.currentLine < dataGridView.RowCount && _reloadMemento.currentLine >= 0)
            {
                dataGridView.CurrentCell = dataGridView.Rows[_reloadMemento.currentLine].Cells[0];
            }
            if (_reloadMemento.firstDisplayedLine < dataGridView.RowCount && _reloadMemento.firstDisplayedLine >= 0)
            {
                dataGridView.FirstDisplayedScrollingRowIndex = _reloadMemento.firstDisplayedLine;
            }
        }

        void LogfileDead()
        {
            Logger.logInfo("File not found.");
            _isDeadFile = true;

            dataGridView.Enabled = false;
            dataGridView.RowCount = 0;
            _progressEventArgs.Visible = false;
            _progressEventArgs.Value = _progressEventArgs.MaxValue;
            SendProgressBarUpdate();
            _statusEventArgs.FileSize = 0;
            _statusEventArgs.LineCount = 0;
            _statusEventArgs.CurrentLineNum = 0;
            SendStatusLineUpdate();
            _shouldCancel = true;
            ClearFilterList();
            BookmarkProvider.ClearAllBookmarks();

            StatusLineText("File not found");
            OnFileNotFound(new EventArgs());
        }

        void LogfileRespawned()
        {
            Logger.logInfo("LogfileDead(): Reloading file because it has been respawned.");
            _isDeadFile = false;
            dataGridView.Enabled = true;
            StatusLineText("");
            OnFileRespawned(new EventArgs());
            Reload();
        }

        void SetGuiAfterLoading()
        {
            if (Text.Length == 0)
            {
                if (IsTempFile)
                {
                    Text = TempTitleName;
                }
                else
                {
                    Text = Util.GetNameFromPath(FileName);
                }
            }
            ShowBookmarkBubbles = Preferences.showBubbles;

            ILogLineColumnizer columnizer;
            if (_forcedColumnizerForLoading != null)
            {
                columnizer = _forcedColumnizerForLoading;
                _forcedColumnizerForLoading = null;
            }
            else
            {
                columnizer = FindColumnizer();
                if (columnizer != null)
                {
                    if (_reloadMemento == null)
                    {
                        columnizer = Util.CloneColumnizer(columnizer);
                    }
                }
                else
                {
                    // Default Columnizers
                    columnizer = Util.CloneColumnizer(PluginRegistry.GetInstance().RegisteredColumnizers[0]);
                }
            }

            Invoke(new Action<ILogLineColumnizer>(SetColumnizer), new object[] { columnizer });
            dataGridView.Enabled = true;
            DisplayCurrentFileOnStatusline();
            _guiStateArgs.MultiFileEnabled = !IsTempFile;
            _guiStateArgs.MenuEnabled = true;
            _guiStateArgs.CurrentEncoding = CurrentLogFileReader.CurrentEncoding;
            SendGuiStateUpdate();

            if (CurrentColumnizer.IsTimeshiftImplemented())
            {
                if (Preferences.timestampControl)
                {
                    SetTimestampLimits();
                    SyncTimestampDisplay();
                }
                Settings settings = ConfigManager.Settings;
                ShowLineColumn(!settings.hideLineColumn);
            }
            ShowTimeSpread(Preferences.showTimeSpread && CurrentColumnizer.IsTimeshiftImplemented());
            locateLineInOriginalFileToolStripMenuItem.Enabled = FilterPipe != null;
        }

        void ReloadNewFile()
        {
            // prevent "overloads". May occur on very fast rollovers (next rollover before the file is reloaded)
            lock (_reloadLock)
            {
                _reloadOverloadCounter++;
                Logger.logInfo("ReloadNewFile(): counter = " + _reloadOverloadCounter);
                if (_reloadOverloadCounter <= 1)
                {
                    SavePersistenceData(false);
                    _loadingFinishedEvent.Reset();
                    _externaLoadingFinishedEvent.Reset();
                    Thread reloadFinishedThread = new Thread(new ThreadStart(ReloadFinishedThreadFx));
                    reloadFinishedThread.IsBackground = true;
                    reloadFinishedThread.Start();
                    LoadFile(FileName, EncodingOptions);

                    BookmarkProvider.ClearAllBookmarks();
                    SavePersistenceData(false);
                }
                else
                {
                    Logger.logDebug("Preventing reload because of recursive calls.");
                }
                _reloadOverloadCounter--;
            }
        }

        void ReloadFinishedThreadFx()
        {
            Logger.logInfo("Waiting for loading to be complete.");
            _loadingFinishedEvent.WaitOne();
            Logger.logInfo("Refreshing filter view because of reload.");
            Invoke(new MethodInvoker(FilterSearch));
            LoadFilterPipes();
            OnFileReloadFinished();
        }

        void LoadingFinished()
        {
            Logger.logInfo("File loading complete.");
            StatusLineText("");
            CurrentLogFileReader.FileSizeChanged += FileSizeChangedHandler;
            _isLoading = false;
            _shouldCancel = false;
            dataGridView.SuspendLayout();
            dataGridView.RowCount = CurrentLogFileReader.LineCount;
            dataGridView.CurrentCellChanged += new EventHandler(DataGridView_CurrentCellChanged);
            dataGridView.Enabled = true;
            dataGridView.AutoResizeColumns(DataGridViewAutoSizeColumnsMode.DisplayedCells);
            dataGridView.ResumeLayout();
            _progressEventArgs.Visible = false;
            _progressEventArgs.Value = _progressEventArgs.MaxValue;
            SendProgressBarUpdate();

            _guiStateArgs.FollowTail = true;
            SendGuiStateUpdate();
            _statusEventArgs.LineCount = CurrentLogFileReader.LineCount;
            _statusEventArgs.FileSize = CurrentLogFileReader.FileSize;
            SendStatusLineUpdate();

            PreferencesChanged(_parentLogTabWin.Preferences, true, SettingsFlags.All);
        }

        void FileSizeChangedHandler(object sender, LogEventArgs e)
        {
            Logger.logInfo("Got FileSizeChanged event. prevLines:" + e.PrevLineCount + ", curr lines: " + e.LineCount);

            lock (_logEventArgsList)
            {
                _logEventArgsList.Add(e);
                _logEventArgsEvent.Set();
            }
        }

        protected void UpdateGrid(LogEventArgs e)
        {
            int oldRowCount = dataGridView.RowCount;
            int firstDisplayedLine = dataGridView.FirstDisplayedScrollingRowIndex;

            try
            {
                if (dataGridView.RowCount > e.LineCount)
                {
                    int currentLineNum = dataGridView.CurrentCellAddress.Y;
                    dataGridView.RowCount = 0;
                    dataGridView.RowCount = e.LineCount;
                    if (!_guiStateArgs.FollowTail)
                    {
                        if (currentLineNum >= dataGridView.RowCount)
                        {
                            currentLineNum = dataGridView.RowCount - 1;
                        }
                        dataGridView.CurrentCell = dataGridView.Rows[currentLineNum].Cells[0];
                    }
                }
                else
                {
                    dataGridView.RowCount = e.LineCount;
                }
                Logger.logDebug("UpdateGrid(): new RowCount=" + dataGridView.RowCount);
                if (e.IsRollover)
                {
                    // Multifile rollover
                    // keep selection and view range, if no follow tail mode
                    if (!_guiStateArgs.FollowTail)
                    {
                        int currentLineNum = dataGridView.CurrentCellAddress.Y;
                        currentLineNum -= e.RolloverOffset;
                        if (currentLineNum < 0)
                        {
                            currentLineNum = 0;
                        }
                        Logger.logDebug("UpdateGrid(): Rollover=true, Rollover offset=" + e.RolloverOffset + ", currLineNum was " + dataGridView.CurrentCellAddress.Y + ", new currLineNum=" + currentLineNum);
                        firstDisplayedLine -= e.RolloverOffset;
                        if (firstDisplayedLine < 0)
                        {
                            firstDisplayedLine = 0;
                        }
                        dataGridView.FirstDisplayedScrollingRowIndex = firstDisplayedLine;
                        dataGridView.CurrentCell = dataGridView.Rows[currentLineNum].Cells[0];
                        dataGridView.Rows[currentLineNum].Selected = true;
                    }
                }
                _statusEventArgs.LineCount = e.LineCount;
                StatusLineFileSize(e.FileSize);

                if (!_isLoading)
                {
                    if (oldRowCount == 0)
                    {
                        AdjustMinimumGridWith();
                    }
                }
                if (_guiStateArgs.FollowTail && dataGridView.RowCount > 0)
                {
                    dataGridView.FirstDisplayedScrollingRowIndex = dataGridView.RowCount - 1;
                    OnTailFollowed(new EventArgs());
                }
                if (Preferences.timestampControl && !_isLoading)
                {
                    SetTimestampLimits();
                }
            }
            catch (Exception ex)
            {
                Logger.logError("Fehler bei UpdateGrid(): " + ex + "\n" + ex.StackTrace);
            }
        }

        protected void CheckFilterAndHighlight(LogEventArgs e)
        {
            bool noLed = true;
            bool suppressLed = false;
            bool setBookmark = false;
            bool stopTail = false;
            string bookmarkComment = null;
            if (filterTailCheckBox.Checked || _filterPipeList.Count > 0)
            {
                int filterStart = e.PrevLineCount;
                if (e.IsRollover)
                {
                    ShiftFilterLines(e.RolloverOffset);
                    filterStart -= e.RolloverOffset;
                }
                bool firstStopTail = true;
                ColumnizerCallback callback = new ColumnizerCallback(this);
                bool filterLineAdded = false;
                for (int i = filterStart; i < e.LineCount; ++i)
                {
                    string line = CurrentLogFileReader.GetLogLine(i);
                    if (line == null)
                    {
                        return;
                    }
                    if (filterTailCheckBox.Checked)
                    {
                        callback.LineNum = i;
                        if (Classes.DamerauLevenshtein.TestFilterCondition(_filterParams, line, callback))
                        {
                            filterLineAdded = true;
                            AddFilterLine(i, false, _filterParams, _filterResultList, _lastFilterLinesList, _filterHitList);
                        }
                    }
                    ProcessFilterPipes(i);

                    IList<HilightEntry> matchingList = FindMatchingHilightEntries(line);
                    LaunchHighlightPlugins(matchingList, i);
                    GetHilightActions(matchingList, out suppressLed, out stopTail, out setBookmark, out bookmarkComment);
                    if (setBookmark)
                    {
                        Action<int, string> fx = new Action<int, string>(SetBookmarkFromTrigger);
                        fx.BeginInvoke(i, bookmarkComment, null, null);
                    }
                    if (stopTail && _guiStateArgs.FollowTail)
                    {
                        bool wasFollow = _guiStateArgs.FollowTail;
                        FollowTailChanged(false, true);
                        if (firstStopTail && wasFollow)
                        {
                            Invoke(new Action<int, bool>(SelectAndEnsureVisible), new object[] { i, false });
                            firstStopTail = false;
                        }
                    }
                    if (!suppressLed)
                    {
                        noLed = false;
                    }
                }
                if (filterLineAdded)
                {
                    TriggerFilterLineGuiUpdate();
                }
            }
            else
            {
                bool firstStopTail = true;
                int startLine = e.PrevLineCount;
                if (e.IsRollover)
                {
                    ShiftFilterLines(e.RolloverOffset);
                    startLine -= e.RolloverOffset;
                }
                for (int i = startLine; i < e.LineCount; ++i)
                {
                    string line = CurrentLogFileReader.GetLogLine(i);
                    if (line != null)
                    {
                        IList<HilightEntry> matchingList = FindMatchingHilightEntries(line);
                        LaunchHighlightPlugins(matchingList, i);
                        GetHilightActions(matchingList, out suppressLed, out stopTail, out setBookmark, out bookmarkComment);
                        if (setBookmark)
                        {
                            Action<int, string> fx = new Action<int, string>(SetBookmarkFromTrigger);
                            fx.BeginInvoke(i, bookmarkComment, null, null);
                        }
                        if (stopTail && _guiStateArgs.FollowTail)
                        {
                            bool wasFollow = _guiStateArgs.FollowTail;
                            FollowTailChanged(false, true);
                            if (firstStopTail && wasFollow)
                            {
                                Invoke(new Action<int, bool>(SelectAndEnsureVisible), new object[] { i, false });
                                firstStopTail = false;
                            }
                        }
                        if (!suppressLed)
                        {
                            noLed = false;
                        }
                    }
                }
            }
            if (!noLed)
            {
                OnFileSizeChanged(e);
            }
        }

        void LaunchHighlightPlugins(IList<HilightEntry> matchingList, int lineNum)
        {
            LogExpertCallback callback = new LogExpertCallback(this);
            callback.LineNum = lineNum;
            foreach (HilightEntry entry in matchingList)
            {
                if (entry.IsActionEntry && entry.ActionEntry.pluginName != null)
                {
                    IKeywordAction plugin = PluginRegistry.GetInstance().FindKeywordActionPluginByName(entry.ActionEntry.pluginName);
                    if (plugin != null)
                    {
                        Action<string, string, ILogExpertCallback, ILogLineColumnizer> fx = new Action<string, string, ILogExpertCallback, ILogLineColumnizer>(plugin.Execute);
                        fx.BeginInvoke(entry.SearchText, entry.ActionEntry.actionParam, callback, CurrentColumnizer, null, null);
                    }
                }
            }
        }

        void AutoResizeColumns(DataGridView gridView)
        {
            try
            {
                gridView.AutoResizeColumns(DataGridViewAutoSizeColumnsMode.DisplayedCells);
                if (gridView.Columns.Count > 1 && Preferences.setLastColumnWidth &&
                    gridView.Columns[gridView.Columns.Count - 1].Width < Preferences.lastColumnWidth)
                {
                    // It seems that using 'MinimumWidth' instead of 'Width' prevents the DataGridView's NullReferenceExceptions
                    //gridView.Columns[gridView.Columns.Count - 1].Width = Preferences.lastColumnWidth;
                    gridView.Columns[gridView.Columns.Count - 1].MinimumWidth = Preferences.lastColumnWidth;
                }
            }
            catch (NullReferenceException e)
            {
                // See https://connect.microsoft.com/VisualStudio/feedback/details/366943/autoresizecolumns-in-datagridview-throws-nullreferenceexception
                // There are some rare situations with null ref exceptions when resizing columns and on filter finished
                // So catch them here. Better than crashing.
                Logger.logError("Error while resizing columns: " + e.Message);
                Logger.logError(e.StackTrace);
            }
        }

        /// <summary>
        /// Builds a list of HilightMatchEntry objects. A HilightMatchEntry spans over a region that is painted with the same foreground and
        /// background colors.
        /// All regions which don't match a word-mode entry will be painted with the colors of a default entry (groundEntry). This is either the
        /// first matching non-word-mode highlight entry or a black-on-white default (if no matching entry was found).
        /// </summary>
        /// <param name="matchList">List of all highlight matches for the current cell</param>
        /// <param name="groundEntry">The entry that is used as the default.</param>
        /// <returns>List of HilightMatchEntry objects. The list spans over the whole cell and contains color infos for every substring.</returns>
        IList<HilightMatchEntry> MergeHighlightMatchEntries(IList<HilightMatchEntry> matchList, HilightMatchEntry groundEntry)
        {
            // Fill an area with lenth of whole text with a default hilight entry
            HilightEntry[] entryArray = new HilightEntry[groundEntry.Length];
            for (int i = 0; i < entryArray.Length; ++i)
            {
                entryArray[i] = groundEntry.HilightEntry;
            }

            // "overpaint" with all matching word match enries
            // Non-word-mode matches will not overpaint because they use the groundEntry
            foreach (HilightMatchEntry me in matchList)
            {
                int endPos = me.StartPos + me.Length;
                for (int i = me.StartPos; i < endPos; ++i)
                {
                    if (me.HilightEntry.IsWordMatch)
                    {
                        entryArray[i] = me.HilightEntry;
                    }
                }
            }

            // collect areas with same hilight entry and build new highlight match entries for it
            IList<HilightMatchEntry> mergedList = new List<HilightMatchEntry>();
            if (entryArray.Length > 0)
            {
                HilightEntry currentEntry = entryArray[0];
                int lastStartPos = 0;
                int pos = 0;
                for (; pos < entryArray.Length; ++pos)
                {
                    if (entryArray[pos] != currentEntry)
                    {
                        HilightMatchEntry me = new HilightMatchEntry();
                        me.StartPos = lastStartPos;
                        me.Length = pos - lastStartPos;
                        me.HilightEntry = currentEntry;
                        mergedList.Add(me);
                        currentEntry = entryArray[pos];
                        lastStartPos = pos;
                    }
                }
                HilightMatchEntry me2 = new HilightMatchEntry();
                me2.StartPos = lastStartPos;
                me2.Length = pos - lastStartPos;
                me2.HilightEntry = currentEntry;
                mergedList.Add(me2);
            }
            return mergedList;
        }

        /**
         * Returns the first HilightEntry that matches the given line
         */
        HilightEntry FindHilightEntry(string line)
        {
            return FindHilightEntry(line, false);
        }

        HilightEntry FindFirstNoWordMatchHilightEntry(string line)
        {
            return FindHilightEntry(line, true);
        }

        bool CheckHighlightEntryMatch(HilightEntry entry, string line)
        {
            if (entry.IsRegEx)
            {
                if (entry.Regex.IsMatch(line))
                {
                    return true;
                }
            }
            else
            {
                if (entry.IsCaseSensitive)
                {
                    if (line.Contains(entry.SearchText))
                    {
                        return true;
                    }
                }
                else
                {
                    if (line.ToLower().Contains(entry.SearchText.ToLower()))
                    {
                        return true;
                    }
                }
            }
            return false;
        }

        /**
         * Returns all HilightEntry entries which matches the given line
         */
        IList<HilightEntry> FindMatchingHilightEntries(string line)
        {
            IList<HilightEntry> resultList = new List<HilightEntry>();
            if (line != null)
            {
                lock (_currentHighlightGroupLock)
                {
                    foreach (HilightEntry entry in _currentHighlightGroup.HilightEntryList)
                    {
                        if (CheckHighlightEntryMatch(entry, line))
                        {
                            resultList.Add(entry);
                        }
                    }
                }
            }
            return resultList;
        }

        void GetHighlightEntryMatches(string line, IList<HilightEntry> hilightEntryList, IList<HilightMatchEntry> resultList)
        {
            foreach (HilightEntry entry in hilightEntryList)
            {
                if (entry.IsWordMatch)
                {
                    MatchCollection matches = entry.Regex.Matches(line);
                    foreach (Match match in matches)
                    {
                        HilightMatchEntry me = new HilightMatchEntry();
                        me.HilightEntry = entry;
                        me.StartPos = match.Index;
                        me.Length = match.Length;
                        resultList.Add(me);
                    }
                }
                else
                {
                    if (CheckHighlightEntryMatch(entry, line))
                    {
                        HilightMatchEntry me = new HilightMatchEntry();
                        me.HilightEntry = entry;
                        me.StartPos = 0;
                        me.Length = line.Length;
                        resultList.Add(me);
                    }
                }
            }
        }

        void GetHilightActions(IList<HilightEntry> matchingList, out bool noLed, out bool stopTail, out bool setBookmark, out string bookmarkComment)
        {
            noLed = stopTail = setBookmark = false;
            bookmarkComment = "";

            foreach (HilightEntry entry in matchingList)
            {
                if (entry.IsLedSwitch)
                {
                    noLed = true;
                }
                if (entry.IsSetBookmark)
                {
                    setBookmark = true;
                    if (entry.BookmarkComment != null && entry.BookmarkComment.Length > 0)
                    {
                        bookmarkComment += entry.BookmarkComment + "\r\n";
                    }
                }
                if (entry.IsStopTail)
                    stopTail = true;
            }
            bookmarkComment.TrimEnd(new char[] { '\r', '\n' });
        }

        void StopTimespreadThread()
        {
            _timeSpreadCalc.Stop();
        }

        void StopTimestampSyncThread()
        {
            _shouldTimestampDisplaySyncingCancel = true;
            _timeshiftSyncWakeupEvent.Set();
            _timeshiftSyncThread.Abort();
            _timeshiftSyncThread.Join();
        }

        void SyncTimestampDisplay()
        {
            if (CurrentColumnizer.IsTimeshiftImplemented())
            {
                if (dataGridView.CurrentRow != null)
                {
                    SyncTimestampDisplay(dataGridView.CurrentRow.Index);
                }
            }
        }

        void SyncTimestampDisplay(int lineNum)
        {
            _timeshiftSyncLine = lineNum;
            _timeshiftSyncTimerEvent.Set();
            _timeshiftSyncWakeupEvent.Set();
        }

        void SyncTimestampDisplayWorker()
        {
            const int WAIT_TIME = 500;
            Thread.CurrentThread.Name = "SyncTimestampDisplayWorker";
            _shouldTimestampDisplaySyncingCancel = false;
            _isTimestampDisplaySyncing = true;

            while (!_shouldTimestampDisplaySyncingCancel)
            {
                _timeshiftSyncWakeupEvent.WaitOne();
                if (_shouldTimestampDisplaySyncingCancel)
                {
                    return;
                }
                _timeshiftSyncWakeupEvent.Reset();

                while (!_shouldTimestampDisplaySyncingCancel)
                {
                    bool signaled = _timeshiftSyncTimerEvent.WaitOne(WAIT_TIME, true);
                    _timeshiftSyncTimerEvent.Reset();
                    if (!signaled)
                    {
                        break;
                    }
                }
                // timeout with no new Trigger -> update display
                int lineNum = _timeshiftSyncLine;
                if (lineNum >= 0 && lineNum < dataGridView.RowCount)
                {
                    int refLine = lineNum;
                    DateTime timeStamp = GetTimestampForLine(ref refLine, true);
                    if (!timeStamp.Equals(DateTime.MinValue) && !_shouldTimestampDisplaySyncingCancel)
                    {
                        _guiStateArgs.Timestamp = timeStamp;
                        SendGuiStateUpdate();
                        if (_shouldCallTimeSync)
                        {
                            refLine = lineNum;
                            DateTime exactTimeStamp = GetTimestampForLine(ref refLine, false);
                            SyncOtherWindows(exactTimeStamp);
                            _shouldCallTimeSync = false;
                        }
                    }
                }
                // show time difference between 2 selected lines
                if (dataGridView.SelectedRows.Count == 2)
                {
                    int row1 = dataGridView.SelectedRows[0].Index;
                    int row2 = dataGridView.SelectedRows[1].Index;
                    if (row1 > row2)
                    {
                        int tmp = row1;
                        row1 = row2;
                        row2 = tmp;
                    }
                    int refLine = row1;
                    DateTime timeStamp1 = GetTimestampForLine(ref refLine, false);
                    refLine = row2;
                    DateTime timeStamp2 = GetTimestampForLine(ref refLine, false);
                    DateTime diff;
                    if (timeStamp1.Ticks > timeStamp2.Ticks)
                    {
                        diff = new DateTime(timeStamp1.Ticks - timeStamp2.Ticks);
                    }
                    else
                    {
                        diff = new DateTime(timeStamp2.Ticks - timeStamp1.Ticks);
                    }
                    StatusLineText("Time diff is " + diff.ToString("HH:mm:ss.fff"));
                }
                else
                {
                    if (!IsMultiFile && dataGridView.SelectedRows.Count == 1)
                    {
                        StatusLineText("");
                    }
                }
            }
        }

        void SyncFilterGridPos()
        {
            try
            {
                if (_filterResultList.Count > 0)
                {
                    int index = _filterResultList.BinarySearch(dataGridView.CurrentRow.Index);
                    if (index < 0)
                    {
                        index = ~index;
                        if (index > 0)
                            --index;
                    }
                    if (filterGridView.Rows.Count > 0)  // exception no rows
                    {
                        filterGridView.CurrentCell = filterGridView.Rows[index].Cells[0];
                    }
                    else
                    {
                        filterGridView.CurrentCell = null;
                    }
                }
            }
            catch (Exception e)
            {
                Logger.logError("SyncFilterGridPos(): " + e.Message);
            }
        }

        void StatusLineFileSize(long size)
        {
            _statusEventArgs.FileSize = size;
            SendStatusLineUpdate();
        }

        void SearchComplete(IAsyncResult result)
        {
            if (Disposing)
                return;
            try
            {
                Invoke(new MethodInvoker(ResetProgressBar));
                AsyncResult ar = (AsyncResult)result;
                Func<SearchParams, int> fx = (Func<SearchParams, int>)ar.AsyncDelegate;
                int line = fx.EndInvoke(result);
                _guiStateArgs.MenuEnabled = true;
                GuiStateUpdate(this, _guiStateArgs);
                if (line == -1)
                {
                    return;
                }
                dataGridView.Invoke(new Action<int, bool>(SelectLine), new object[] { line, true });
            }
            catch (Exception) // in the case the windows is already destroyed
            {
            }
        }

        void ResetProgressBar()
        {
            _progressEventArgs.Value = _progressEventArgs.MaxValue;
            _progressEventArgs.Visible = false;
            SendProgressBarUpdate();
        }

        void SelectLine(int line, bool triggerSyncCall)
        {
            SelectLine(line, triggerSyncCall, true);
        }

        void SelectLine(int line, bool triggerSyncCall, bool shouldScroll)
        {
            try
            {
                _shouldCallTimeSync = triggerSyncCall;
                bool wasCancelled = _shouldCancel;
                _shouldCancel = false;
                _isSearching = false;
                StatusLineText("");
                _guiStateArgs.MenuEnabled = true;
                if (wasCancelled)
                {
                    return;
                }
                if (line == -1)
                {
                    MessageBox.Show(this, "Not found:", "Search result");   // Hmm... is that experimental code from early days?
                    return;
                }
                dataGridView.Rows[line].Selected = true;
                if (shouldScroll)
                {
                    dataGridView.CurrentCell = dataGridView.Rows[line].Cells[0];
                    dataGridView.Focus();
                }
            }
            catch (IndexOutOfRangeException e)
            {
                // Occures sometimes (but cannot reproduce)
                Logger.logError("Error while selecting line: " + e.ToString());
            }
        }

        void SelectAndScrollToLine(int line)
        {
            SelectLine(line, false);
            dataGridView.FirstDisplayedScrollingRowIndex = line;
        }

        public void LogWindow_KeyDown(object sender, KeyEventArgs e)
        {
            if (_isErrorShowing)
            {
                RemoveStatusLineError();
            }
            if (e.KeyCode == Keys.F3)
            {
                if (_parentLogTabWin.SearchParams == null ||
                    _parentLogTabWin.SearchParams.searchText == null ||
                    _parentLogTabWin.SearchParams.searchText.Length == 0)
                {
                    return;
                }
                _parentLogTabWin.SearchParams.isFindNext = true;
                _parentLogTabWin.SearchParams.isShiftF3Pressed = ((e.Modifiers & Keys.Shift) == Keys.Shift);
                StartSearch();
            }
            if (e.KeyCode == Keys.Escape)
            {
                if (_isSearching)
                {
                    _shouldCancel = true;
                }
                FireCancelHandlers();
                RemoveAllSearchHighlightEntries();
            }
            if (e.KeyCode == Keys.E && (e.Modifiers & Keys.Control) == Keys.Control)
            {
                StartEditMode();
            }
            if (e.KeyCode == Keys.Down && e.Modifiers == Keys.Alt)
            {
                int newLine = CurrentLogFileReader.GetNextMultiFileLine(dataGridView.CurrentCellAddress.Y);
                if (newLine != -1)
                {
                    SelectLine(newLine, false);
                }
                e.Handled = true;
            }
            if (e.KeyCode == Keys.Up && e.Modifiers == Keys.Alt)
            {
                int newLine = CurrentLogFileReader.GetPrevMultiFileLine(dataGridView.CurrentCellAddress.Y);
                if (newLine != -1)
                {
                    SelectLine(newLine - 1, false);
                }
                e.Handled = true;
            }
            if (e.KeyCode == Keys.Enter && dataGridView.Focused)
            {
                ChangeRowHeight(e.Shift);
                e.Handled = true;
            }
            if (e.KeyCode == Keys.Back && dataGridView.Focused)
            {
                ChangeRowHeight(true);
                e.Handled = true;
            }
            if (e.KeyCode == Keys.PageUp && e.Modifiers == Keys.Alt)
            {
                SelectPrevHighlightLine();
                e.Handled = true;
            }
            if (e.KeyCode == Keys.PageDown && e.Modifiers == Keys.Alt)
            {
                SelectNextHighlightLine();
                e.Handled = true;
            }
            if (e.KeyCode == Keys.T && (e.Modifiers & Keys.Control) == Keys.Control && (e.Modifiers & Keys.Shift) == Keys.Shift)
            {
                FilterToTab();
            }
        }

        void StartEditMode()
        {
            if (!dataGridView.CurrentCell.ReadOnly)
            {
                dataGridView.BeginEdit(false);
                if (dataGridView.EditingControl != null)
                {
                    if (dataGridView.EditingControl.GetType().IsAssignableFrom(typeof(LogCellEditingControl)))
                    {
                        DataGridViewTextBoxEditingControl editControl = dataGridView.EditingControl as DataGridViewTextBoxEditingControl;
                        editControl.KeyDown += EditControl_UpdateEditColumnDisplay;
                        editControl.KeyPress += new KeyPressEventHandler(EditControl_KeyPress);
                        editControl.KeyUp += new KeyEventHandler(EditControl_UpdateEditColumnDisplay);
                        editControl.Click += new EventHandler(EditControl_Click);
                        dataGridView.CellEndEdit += new DataGridViewCellEventHandler(DataGridView_CellEndEdit);
                        editControl.SelectionStart = 0;
                    }
                }
            }
        }

        void UpdateEditColumnDisplay(DataGridViewTextBoxEditingControl editControl)
        {
            // prevents key events after edit mode has ended
            if (dataGridView.EditingControl != null)
            {
                int pos = editControl.SelectionStart + editControl.SelectionLength;
                StatusLineText("   " + pos);
                Logger.logDebug("SelStart: " + editControl.SelectionStart + ", SelLen: " + editControl.SelectionLength);
            }
        }

        void SelectPrevHighlightLine()
        {
            int lineNum = dataGridView.CurrentCellAddress.Y;
            while (lineNum > 0)
            {
                lineNum--;
                string line = CurrentLogFileReader.GetLogLine(lineNum);
                if (line != null)
                {
                    HilightEntry entry = FindHilightEntry(line);
                    if (entry != null)
                    {
                        SelectLine(lineNum, false);
                        break;
                    }
                }
            }
        }

        void SelectNextHighlightLine()
        {
            int lineNum = dataGridView.CurrentCellAddress.Y;
            while (lineNum < CurrentLogFileReader.LineCount)
            {
                lineNum++;
                string line = CurrentLogFileReader.GetLogLine(lineNum);
                if (line != null)
                {
                    HilightEntry entry = FindHilightEntry(line);
                    if (entry != null)
                    {
                        SelectLine(lineNum, false);
                        break;
                    }
                }
            }
        }

        int FindNextBookmarkIndex(int lineNum, bool isForward)
        {
            lineNum = dataGridView.RowCount.GetNextIndex(lineNum, isForward);

            if (isForward)
            {
                return BookmarkProvider.FindNextBookmarkIndex(lineNum);
            }
            else
            {
                return BookmarkProvider.FindPrevBookmarkIndex(lineNum);
            }
        }

        /**
         * Shift bookmarks after a logfile rollover
         */
        void ShiftBookmarks(int offset)
        {
            BookmarkProvider.ShiftBookmarks(offset);
        }

        void LoadFilterPipes()
        {
            lock (_filterPipeList)
            {
                foreach (FilterPipe pipe in _filterPipeList)
                {
                    pipe.RecreateTempFile();
                }
            }
            if (_filterPipeList.Count > 0)
            {
                for (int i = 0; i < dataGridView.RowCount; ++i)
                {
                    ProcessFilterPipes(i);
                }
            }
        }

        void DisconnectFilterPipes()
        {
            lock (_filterPipeList)
            {
                foreach (FilterPipe pipe in _filterPipeList)
                {
                    pipe.ClearLineList();
                }
            }
        }

        // ======================================================================================
        // Filter Grid stuff
        // ======================================================================================

        void ApplyFilterParams()
        {
            filterComboBox.Text = _filterParams.searchText;
            filterCaseSensitiveCheckBox.Checked = _filterParams.isCaseSensitive;
            filterRegexCheckBox.Checked = _filterParams.isRegex;
            filterTailCheckBox.Checked = _filterParams.isFilterTail;
            invertFilterCheckBox.Checked = _filterParams.isInvert;
            filterKnobControl1.Value = _filterParams.spreadBefore;
            filterKnobControl2.Value = _filterParams.spreadBehind;
            rangeCheckBox.Checked = _filterParams.isRangeSearch;
            columnRestrictCheckBox.Checked = _filterParams.columnRestrict;
            fuzzyKnobControl.Value = _filterParams.fuzzyValue;
            filterRangeComboBox.Text = _filterParams.rangeSearchText;
        }

        void ResetFilterControls()
        {
            filterComboBox.Text = "";
            filterCaseSensitiveCheckBox.Checked = false;
            filterRegexCheckBox.Checked = false;
            invertFilterCheckBox.Checked = false;
            filterKnobControl1.Value = 0;
            filterKnobControl2.Value = 0;
            rangeCheckBox.Checked = false;
            columnRestrictCheckBox.Checked = false;
            fuzzyKnobControl.Value = 0;
            filterRangeComboBox.Text = "";
        }

        void FilterSearch()
        {
            if (filterComboBox.Text.Length == 0)
            {
                _filterParams.searchText = "";
                _filterParams.lowerSearchText = "";
                _filterParams.isRangeSearch = false;
                ClearFilterList();
                filterSearchButton.Image = null;
                ResetFilterControls();
                saveFilterButton.Enabled = false;
                return;
            }
            FilterSearch(filterComboBox.Text);
        }

        void FilterSearch(string text)
        {
            FireCancelHandlers();   // make sure that there's no other filter running (maybe from filter restore)

            _filterParams.searchText = text;
            _filterParams.lowerSearchText = text.ToLower();
            ConfigManager.Settings.filterHistoryList.Remove(text);
            ConfigManager.Settings.filterHistoryList.Insert(0, text);
            if (ConfigManager.Settings.filterHistoryList.Count > MAX_HISTORY)
            {
                ConfigManager.Settings.filterHistoryList.RemoveAt(filterComboBox.Items.Count - 1);
            }
            filterComboBox.Items.Clear();
            foreach (string item in ConfigManager.Settings.filterHistoryList)
            {
                filterComboBox.Items.Add(item);
            }
            filterComboBox.Text = text;

            _filterParams.isRangeSearch = rangeCheckBox.Checked;
            _filterParams.rangeSearchText = filterRangeComboBox.Text;
            if (_filterParams.isRangeSearch)
            {
                ConfigManager.Settings.filterRangeHistoryList.Remove(filterRangeComboBox.Text);
                ConfigManager.Settings.filterRangeHistoryList.Insert(0, filterRangeComboBox.Text);
                if (ConfigManager.Settings.filterRangeHistoryList.Count > MAX_HISTORY)
                {
                    ConfigManager.Settings.filterRangeHistoryList.RemoveAt(filterRangeComboBox.Items.Count - 1);
                }

                filterRangeComboBox.Items.Clear();
                foreach (string item in ConfigManager.Settings.filterRangeHistoryList)
                {
                    filterRangeComboBox.Items.Add(item);
                }
            }
            ConfigManager.Save(SettingsFlags.FilterHistory);

            _filterParams.isCaseSensitive = filterCaseSensitiveCheckBox.Checked;
            _filterParams.isRegex = filterRegexCheckBox.Checked;
            _filterParams.isFilterTail = filterTailCheckBox.Checked;
            _filterParams.isInvert = invertFilterCheckBox.Checked;
            if (_filterParams.isRegex)
            {
                try
                {
                    _filterParams.CreateRegex();
                }
                catch (ArgumentException)
                {
                    StatusLineError("Invalid regular expression");
                    return;
                }
            }
            _filterParams.fuzzyValue = fuzzyKnobControl.Value;
            _filterParams.spreadBefore = filterKnobControl1.Value;
            _filterParams.spreadBehind = filterKnobControl2.Value;
            _filterParams.columnRestrict = columnRestrictCheckBox.Checked;

            //ConfigManager.SaveFilterParams(filterParams);
            ConfigManager.Settings.filterParams = _filterParams;  // wozu eigentlich? sinnlos seit MDI?

            _shouldCancel = false;
            _isSearching = true;
            filterSearchButton.Enabled = false;
            ClearFilterList();

            StartProgressBar(dataGridView.RowCount, "Filtering... Press ESC to cancel");

            Settings settings = ConfigManager.Settings;
            Action<FilterParams, List<int>, List<int>, List<int>> fx;
            fx = settings.preferences.multiThreadFilter ? new Action<FilterParams, List<int>, List<int>, List<int>>(MultiThreadedFilter) : new Action<FilterParams, List<int>, List<int>, List<int>>(Filter);
            fx.BeginInvoke(_filterParams, _filterResultList, _lastFilterLinesList, _filterHitList, FilterComplete, null);
            CheckForFilterDirty();
        }

        void MultiThreadedFilter(FilterParams filterParams, List<int> filterResultLines, List<int> lastFilterLinesList, List<int> filterHitList)
        {
            ColumnizerCallback callback = new ColumnizerCallback(this);
            FilterStarter fs = new FilterStarter(callback, Environment.ProcessorCount + 2);
            fs.FilterHitList = _filterHitList;
            fs.FilterResultLines = _filterResultList;
            fs.LastFilterLinesList = _lastFilterLinesList;
            BackgroundProcessCancelHandler cancelHandler = new FilterCancelHandler(fs);
            RegisterCancelHandler(cancelHandler);
            long startTime = Environment.TickCount;

            fs.DoFilter(filterParams, 0, CurrentLogFileReader.LineCount, FilterProgressCallback);

            long endTime = Environment.TickCount;
#if DEBUG
            Logger.logInfo("Multi threaded filter duration: " + ((endTime - startTime)) + " ms.");
#endif
            DeRegisterCancelHandler(cancelHandler);
            StatusLineText("Filter duration: " + ((endTime - startTime)) + " ms.");
        }

        void FilterProgressCallback(int lineCount)
        {
            UpdateProgressBar(lineCount);
        }

        void Filter(FilterParams filterParams, List<int> filterResultLines, List<int> lastFilterLinesList, List<int> filterHitList)
        {
            long startTime = Environment.TickCount;
            try
            {
                filterParams.Reset();
                int lineNum = 0;
                ColumnizerCallback callback = new ColumnizerCallback(this);
                while (true)
                {
                    string line = CurrentLogFileReader.GetLogLine(lineNum);
                    if (line == null)
                    {
                        break;
                    }
                    callback.LineNum = lineNum;
                    if (Classes.DamerauLevenshtein.TestFilterCondition(filterParams, line, callback))
                    {
                        AddFilterLine(lineNum, false, filterParams, filterResultLines, lastFilterLinesList, filterHitList);
                    }
                    lineNum++;
                    if (lineNum % PROGRESS_BAR_MODULO == 0)
                    {
                        UpdateProgressBar(lineNum);
                    }
                    if (_shouldCancel)
                    {
                        break;
                    }
                }
            }
            catch (Exception ex)
            {
                Logger.logError("Exception while filtering. Please report to developer: \n\n" + ex + "\n\n" + ex.StackTrace);
                MessageBox.Show(null, "Exception while filtering. Please report to developer: \n\n" + ex + "\n\n" + ex.StackTrace, "LogExpert");
            }
            long endTime = Environment.TickCount;
#if DEBUG
            Logger.logInfo("Single threaded filter duration: " + ((endTime - startTime)) + " ms.");
#endif
            StatusLineText("Filter duration: " + ((endTime - startTime)) + " ms.");
        }

        /// <summary>
        ///  Returns a list with 'additional filter results'. This is the given line number
        ///  and (if back spread and/or fore spread is enabled) some additional lines.
        ///  This function doesn't check the filter condition!
        /// </summary>
        /// <param name="filterParams"></param>
        /// <param name="lineNum"></param>
        /// <param name="checkList"></param>
        /// <returns></returns>
        IList<int> GetAdditionalFilterResults(FilterParams filterParams, int lineNum, IList<int> checkList)
        {
            IList<int> resultList = new List<int>();

            if (filterParams.spreadBefore == 0 && filterParams.spreadBehind == 0)
            {
                resultList.Add(lineNum);
                return resultList;
            }

            // back spread
            for (int i = filterParams.spreadBefore; i > 0; --i)
            {
                if (lineNum - i > 0)
                {
                    if (!resultList.Contains(lineNum - i) && !checkList.Contains(lineNum - i))
                    {
                        resultList.Add(lineNum - i);
                    }
                }
            }
            // direct filter hit
            if (!resultList.Contains(lineNum) && !checkList.Contains(lineNum))
            {
                resultList.Add(lineNum);
            }
            // after spread
            for (int i = 1; i <= filterParams.spreadBehind; ++i)
            {
                if (lineNum + i < CurrentLogFileReader.LineCount)
                {
                    if (!resultList.Contains(lineNum + i) && !checkList.Contains(lineNum + i))
                    {
                        resultList.Add(lineNum + i);
                    }
                }
            }
            return resultList;
        }

        void AddFilterLine(int lineNum, bool immediate, FilterParams filterParams, List<int> filterResultLines, List<int> lastFilterLinesList, List<int> filterHitList)
        {
            lock (_filterResultList)
            {
                filterHitList.Add(lineNum);
                IList<int> filterResult = GetAdditionalFilterResults(filterParams, lineNum, lastFilterLinesList);
                filterResultLines.AddRange(filterResult);
                lastFilterLinesList.AddRange(filterResult);
                if (lastFilterLinesList.Count > SPREAD_MAX * 2)
                {
                    lastFilterLinesList.RemoveRange(0, lastFilterLinesList.Count - SPREAD_MAX * 2);
                }
            }
            if (immediate)
            {
                TriggerFilterLineGuiUpdate();
            }
        }

        void TriggerFilterLineGuiUpdate()
        {
            Invoke(new MethodInvoker(AddFilterLineGuiUpdate));
        }

        void AddFilterLineGuiUpdate()
        {
            try
            {
                lock (_filterResultList)
                {
                    filterCountLabel.Text = "" + _filterResultList.Count;
                    if (filterGridView.RowCount > _filterResultList.Count)
                    {
                        filterGridView.RowCount = 0;  // helps to prevent hang ?
                    }
                    filterGridView.RowCount = _filterResultList.Count;
                    if (filterGridView.RowCount > 0)
                    {
                        filterGridView.FirstDisplayedScrollingRowIndex = filterGridView.RowCount - 1;
                    }
                    if (filterGridView.RowCount == 1)
                    {
                        // after a file reload adjusted column sizes anew when the first line arrives
                        //filterGridView.AutoResizeColumns(DataGridViewAutoSizeColumnsMode.DisplayedCells);
                        AutoResizeColumns(filterGridView);
                    }
                }
            }
            catch (Exception e)
            {
                Logger.logError("AddFilterLineGuiUpdate(): " + e.Message);
            }
        }

        protected void UpdateProgressBar(int value)
        {
            _progressEventArgs.Value = value;
            if (value > _progressEventArgs.MaxValue)
            {
                // can occur if new lines will be added while filtering
                _progressEventArgs.MaxValue = value;
            }
            SendProgressBarUpdate();
        }

        void FilterComplete(IAsyncResult result)
        {
            if (!IsDisposed && !_waitingForClose && !Disposing)
            {
                Invoke(new MethodInvoker(ResetStatusAfterFilter));
            }
        }

        void ResetStatusAfterFilter()
        {
            try
            {
                _isSearching = false;
                _progressEventArgs.Value = _progressEventArgs.MaxValue;
                _progressEventArgs.Visible = false;
                SendProgressBarUpdate();
                filterGridView.RowCount = _filterResultList.Count;
                AutoResizeColumns(filterGridView);
                filterCountLabel.Text = "" + _filterResultList.Count;
                if (filterGridView.RowCount > 0)
                {
                    filterGridView.Focus();
                }
                filterSearchButton.Enabled = true;
            }
            catch (NullReferenceException e)
            {
                // See https://connect.microsoft.com/VisualStudio/feedback/details/366943/autoresizecolumns-in-datagridview-throws-nullreferenceexception
                // There are some rare situations with null ref exceptions when resizing columns and on filter finished
                // So catch them here. Better than crashing.
                Logger.logError("Error: " + e.Message);
                Logger.logError(e.StackTrace);
            }
        }

        protected void ClearFilterList()
        {
            try
            {
                lock (_filterResultList)
                {
                    filterGridView.SuspendLayout();
                    filterGridView.RowCount = 0;
                    filterCountLabel.Text = "0";
                    _filterResultList = new List<int>();
                    _lastFilterLinesList = new List<int>();
                    _filterHitList = new List<int>();
                    filterGridView.ResumeLayout();
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show(null, ex.StackTrace, "Wieder dieser sporadische Fehler:");
                Logger.logError("Wieder dieser sporadische Fehler: " + ex + "\n" + ex.StackTrace);
            }
        }

        /**
         * Shift filter list line entries after a logfile rollover
         */
        void ShiftFilterLines(int offset)
        {
            List<int> newFilterList = new List<int>();
            lock (_filterResultList)
            {
                foreach (int lineNum in _filterResultList)
                {
                    int line = lineNum - offset;
                    if (line >= 0)
                    {
                        newFilterList.Add(line);
                    }
                }
                _filterResultList = newFilterList;
            }

            newFilterList = new List<int>();
            foreach (int lineNum in _filterHitList)
            {
                int line = lineNum - offset;
                if (line >= 0)
                {
                    newFilterList.Add(line);
                }
            }
            _filterHitList = newFilterList;

            int count = SPREAD_MAX;
            if (_filterResultList.Count < SPREAD_MAX)
            {
                count = _filterResultList.Count;
            }
            _lastFilterLinesList = _filterResultList.GetRange(_filterResultList.Count - count, count);

            TriggerFilterLineGuiUpdate();
        }

        void CheckForFilterDirty()
        {
            if (IsFilterSearchDirty(_filterParams))
            {
                filterSearchButton.Image = _searchButtonImage;
                saveFilterButton.Enabled = false;
            }
            else
            {
                filterSearchButton.Image = null;
                saveFilterButton.Enabled = true;
            }
        }

        bool IsFilterSearchDirty(FilterParams filterParams)
        {
            if (!filterParams.searchText.Equals(filterComboBox.Text))
            {
                return true;
            }
            if (filterParams.isRangeSearch != rangeCheckBox.Checked)
            {
                return true;
            }
            if (filterParams.isRangeSearch && !filterParams.rangeSearchText.Equals(filterRangeComboBox.Text))
            {
                return true;
            }
            if (filterParams.isRegex != filterRegexCheckBox.Checked)
            {
                return true;
            }
            if (filterParams.isInvert != invertFilterCheckBox.Checked)
            {
                return true;
            }
            if (filterParams.spreadBefore != filterKnobControl1.Value)
            {
                return true;
            }
            if (filterParams.spreadBehind != filterKnobControl2.Value)
            {
                return true;
            }
            if (filterParams.fuzzyValue != fuzzyKnobControl.Value)
            {
                return true;
            }
            if (filterParams.columnRestrict != columnRestrictCheckBox.Checked)
            {
                return true;
            }
            if (filterParams.isCaseSensitive != filterCaseSensitiveCheckBox.Checked)
            {
                return true;
            }
            return false;
        }

        void AdjustMinimumGridWith()
        {
            if (dataGridView.Columns.Count > 1)
            {
                AutoResizeColumns(dataGridView);

                int width = dataGridView.Columns.GetColumnsWidth(DataGridViewElementStates.Visible);
                int diff = dataGridView.Width - width;
                if (diff > 0)
                {
                    diff -= dataGridView.RowHeadersWidth / 2;
                    dataGridView.Columns[dataGridView.Columns.Count - 1].Width =
                                                                                dataGridView.Columns[dataGridView.Columns.Count - 1].Width + diff;
                    filterGridView.Columns[filterGridView.Columns.Count - 1].Width =
                                                                                    filterGridView.Columns[filterGridView.Columns.Count - 1].Width + diff;
                }
            }
        }

        public void ToggleFilterPanel()
        {
            splitContainer1.Panel2Collapsed = !splitContainer1.Panel2Collapsed;
            if (!splitContainer1.Panel2Collapsed)
            {
                filterComboBox.Focus();
            }
            else
            {
                dataGridView.Focus();
            }
        }

        void InvalidateCurrentRow(DataGridView gridView)
        {
            if (gridView.CurrentCellAddress.Y > -1)
            {
                gridView.InvalidateRow(gridView.CurrentCellAddress.Y);
            }
        }

        void InvalidateCurrentRow()
        {
            InvalidateCurrentRow(dataGridView);
            InvalidateCurrentRow(filterGridView);
        }

        void DisplayCurrentFileOnStatusline()
        {
            if (CurrentLogFileReader.IsMultiFile)
            {
                try
                {
                    if (dataGridView.CurrentRow != null && dataGridView.CurrentRow.Index > -1)
                    {
                        string fileName =
                            CurrentLogFileReader.GetLogFileNameForLine(dataGridView.CurrentRow.Index);
                        if (fileName != null)
                        {
                            StatusLineText(Util.GetNameFromPath(fileName));
                        }
                    }
                }
                catch (Exception)
                {
                    // TODO: handle this concurrent situation better:
                    // dataGridView.CurrentRow may be null even if checked before.
                    // This can happen when MultiFile shift deselects the current row because there
                    // are less lines after rollover than before.
                    // access to dataGridView-Rows should be locked
                }
            }
        }

        void UpdateSelectionDisplay()
        {
            if (_noSelectionUpdates)
            {
                return;
            }
            _selectionChangedTrigger.Trigger();
        }

        void UpdateFilterHistoryFromSettings()
        {
            ConfigManager.Settings.filterHistoryList = ConfigManager.Settings.filterHistoryList;
            filterComboBox.Items.Clear();
            foreach (string item in ConfigManager.Settings.filterHistoryList)
            {
                filterComboBox.Items.Add(item);
            }

            filterRangeComboBox.Items.Clear();
            foreach (string item in ConfigManager.Settings.filterRangeHistoryList)
            {
                filterRangeComboBox.Items.Add(item);
            }
        }

        void StatusLineText(string text)
        {
            _statusEventArgs.StatusText = text;
            SendStatusLineUpdate();
        }

        void StatusLineTextImmediate(string text)
        {
            _statusEventArgs.StatusText = text;
            _statusLineTrigger.TriggerImmediate();
        }

        protected void StatusLineError(string text)
        {
            StatusLineText(text);
            _isErrorShowing = true;
        }

        void RemoveStatusLineError()
        {
            StatusLineText("");
            _isErrorShowing = false;
        }

        void SendGuiStateUpdate()
        {
            OnGuiState(_guiStateArgs);
        }

        void ShowAdvancedFilterPanel(bool show)
        {
            if (show)
            {
                advancedButton.Text = "Hide advanced...";
                advancedButton.Image = null;
            }
            else
            {
                advancedButton.Text = "Show advanced...";
                CheckForAdvancedButtonDirty();
            }

            advancedFilterSplitContainer.Panel1Collapsed = !show;
            advancedFilterSplitContainer.SplitterDistance = 54;
            _showAdvanced = show;
        }

        void CheckForAdvancedButtonDirty()
        {
            if (IsAdvancedOptionActive() && !_showAdvanced)
            {
                advancedButton.Image = _advancedButtonImage;
            }
            else
            {
                advancedButton.Image = null;
            }
        }

        void FilterToTab()
        {
            filterSearchButton.Enabled = false;
            MethodInvoker invoker = new MethodInvoker(WriteFilterToTab);
            invoker.BeginInvoke(null, null);
        }

        void WriteFilterToTab()
        {
            FilterPipe pipe = new FilterPipe(_filterParams.CreateCopy(), this);
            lock (_filterResultList)
            {
                string namePrefix = "->F";
                string title;
                if (IsTempFile)
                {
                    title = TempTitleName + namePrefix + ++_filterPipeNameCounter;
                }
                else
                {
                    title = Util.GetNameFromPath(FileName) + namePrefix + ++_filterPipeNameCounter;
                }

                WritePipeToTab(pipe, _filterResultList, title, null);
            }
        }

        void WritePipeToTab(FilterPipe pipe, IList<int> lineNumberList, string name, PersistenceData persistenceData)
        {
            Logger.logInfo("WritePipeToTab(): " + lineNumberList.Count + " lines.");
            _guiStateArgs.MenuEnabled = false;
            SendGuiStateUpdate();

            StartProgressBar(lineNumberList.Count, "Writing to temp file... Press ESC to cancel.");

            _isSearching = true;
            _shouldCancel = false;

            lock (_filterPipeList)
            {
                _filterPipeList.Add(pipe);
            }
            pipe.Closed += new FilterPipe.ClosedEventHandler(Pipe_Disconnected);
            int count = 0;
            pipe.OpenFile();
            LogExpertCallback callback = new LogExpertCallback(this);
            foreach (int i in lineNumberList)
            {
                if (_shouldCancel)
                {
                    break;
                }
                string line = CurrentLogFileReader.GetLogLine(i);
                if (CurrentColumnizer is ILogLineXmlColumnizer)
                {
                    callback.LineNum = i;
                    line = (CurrentColumnizer as ILogLineXmlColumnizer).GetLineTextForClipboard(line, callback);
                }
                pipe.WriteToPipe(line, i);
                if (++count % PROGRESS_BAR_MODULO == 0)
                {
                    _progressEventArgs.Value = count;
                    Invoke(new MethodInvoker(SendProgressBarUpdate));
                }
            }
            pipe.CloseFile();
            Logger.logInfo("WritePipeToTab(): finished");
            Invoke(new Action<FilterPipe, string, PersistenceData>(WriteFilterToTabFinished), new object[] { pipe, name, persistenceData });
        }

        void WriteFilterToTabFinished(FilterPipe pipe, string name, PersistenceData persistenceData)
        {
            _isSearching = false;
            if (!_shouldCancel)
            {
                string title = name;
                ILogLineColumnizer preProcessColumnizer = null;
                if (!(CurrentColumnizer is ILogLineXmlColumnizer))
                {
                    preProcessColumnizer = CurrentColumnizer;
                }
                LogWindow newWin = _parentLogTabWin.AddFilterTab(pipe, title, preProcessColumnizer);
                newWin.FilterPipe = pipe;
                pipe.OwnLogWindow = newWin;
                if (persistenceData != null)
                {
                    Action<LogWindow, PersistenceData> fx = new Action<LogWindow, PersistenceData>(FilterRestore);
                    fx.BeginInvoke(newWin, persistenceData, null, null);
                }
            }
            _progressEventArgs.Value = _progressEventArgs.MaxValue;
            _progressEventArgs.Visible = false;
            SendProgressBarUpdate();
            _guiStateArgs.MenuEnabled = true;
            SendGuiStateUpdate();
            StatusLineText("");
            filterSearchButton.Enabled = true;
        }

        void FilterRestore(LogWindow newWin, PersistenceData persistenceData)
        {
            newWin.WaitForLoadingFinished();
            ILogLineColumnizer columnizer = Util.FindColumnizerByName(persistenceData.columnizerName, PluginRegistry.GetInstance().RegisteredColumnizers);
            if (columnizer != null)
            {
                Action<ILogLineColumnizer> fx = new Action<ILogLineColumnizer>(newWin.ForceColumnizer);
                newWin.Invoke(fx, new object[] { columnizer });
            }
            else
            {
                Logger.logWarn("FilterRestore(): Columnizer " + persistenceData.columnizerName + " not found");
            }
            newWin.BeginInvoke(new Action<PersistenceData>(newWin.RestoreFilters), new object[] { persistenceData });
        }

        void ProcessFilterPipes(int lineNum)
        {
            string searchLine = CurrentLogFileReader.GetLogLine(lineNum);
            if (searchLine == null)
            {
                return;
            }

            ColumnizerCallback callback = new ColumnizerCallback(this);
            callback.LineNum = lineNum;
            IList<FilterPipe> deleteList = new List<FilterPipe>();
            lock (_filterPipeList)
            {
                foreach (FilterPipe pipe in _filterPipeList)
                {
                    if (pipe.IsStopped)
                    {
                        continue;
                    }
                    if (Classes.DamerauLevenshtein.TestFilterCondition(pipe.FilterParams, searchLine, callback))
                    {
                        IList<int> filterResult = GetAdditionalFilterResults(pipe.FilterParams, lineNum, pipe.LastLinesHistoryList);
                        pipe.OpenFile();
                        foreach (int line in filterResult)
                        {
                            pipe.LastLinesHistoryList.Add(line);
                            if (pipe.LastLinesHistoryList.Count > SPREAD_MAX * 2)
                            {
                                pipe.LastLinesHistoryList.RemoveAt(0);
                            }

                            string textLine = CurrentLogFileReader.GetLogLine(line);
                            bool fileOk = pipe.WriteToPipe(textLine, line);
                            if (!fileOk)
                            {
                                deleteList.Add(pipe);
                            }
                        }
                        pipe.CloseFile();
                    }
                }
            }
            foreach (FilterPipe pipe in deleteList)
            {
                _filterPipeList.Remove(pipe);
            }
        }

        void CopyMarkedLinesToClipboard()
        {
            if (_guiStateArgs.CellSelectMode)
            {
                DataObject data = dataGridView.GetClipboardContent();
                Clipboard.SetDataObject(data);
            }
            else
            {
                List<int> lineNumList = new List<int>();
                foreach (DataGridViewRow row in dataGridView.SelectedRows)
                {
                    if (row.Index != -1)
                    {
                        lineNumList.Add(row.Index);
                    }
                }
                lineNumList.Sort();
                StringBuilder clipText = new StringBuilder();
                LogExpertCallback callback = new LogExpertCallback(this);
                foreach (int lineNum in lineNumList)
                {
                    string line = CurrentLogFileReader.GetLogLine(lineNum);
                    if (CurrentColumnizer is ILogLineXmlColumnizer)
                    {
                        callback.LineNum = lineNum;
                        line = (CurrentColumnizer as ILogLineXmlColumnizer).GetLineTextForClipboard(line, callback);
                    }
                    clipText.AppendLine(line);
                }
                Clipboard.SetText(clipText.ToString());
            }
        }

        void ApplyDataGridViewPrefs(DataGridView dataGridView, Preferences prefs)
        {
            if (dataGridView.Columns.Count > 1)
            {
                if (prefs.setLastColumnWidth)
                {
                    dataGridView.Columns[dataGridView.Columns.Count - 1].MinimumWidth = prefs.lastColumnWidth;
                }
                else
                {
                    // Workaround for a .NET bug which brings the DataGridView into an unstable state (causing lots of NullReferenceExceptions).
                    dataGridView.FirstDisplayedScrollingColumnIndex = 0;

                    dataGridView.Columns[dataGridView.Columns.Count - 1].MinimumWidth = 5;  // default
                }
            }
            if (dataGridView.RowCount > 0)
            {
                dataGridView.UpdateRowHeightInfo(0, true);
            }
            dataGridView.Invalidate();
            dataGridView.Refresh();
            AutoResizeColumns(dataGridView);
        }

        IList<int> GetSelectedContent()
        {
            if (dataGridView.SelectionMode == DataGridViewSelectionMode.FullRowSelect)
            {
                List<int> lineNumList = new List<int>();
                foreach (DataGridViewRow row in dataGridView.SelectedRows)
                {
                    if (row.Index != -1)
                    {
                        lineNumList.Add(row.Index);
                    }
                }
                lineNumList.Sort();
                return lineNumList;
            }
            return new List<int>();
        }

        void BookmarkComment(Bookmark bookmark)
        {
            BookmarkCommentDlg dlg = new BookmarkCommentDlg();
            dlg.Comment = bookmark.Text;
            if (dlg.ShowDialog() == DialogResult.OK)
            {
                BookmarkProvider.UpdateBookmarkText(bookmark, dlg.Comment);
                dataGridView.Refresh();
            }
        }

        /// <summary>
        /// Indicates which columns we are filtering on
        /// </summary>
        /// <param name="filter"></param>
        /// <returns></returns>
        string CalculateColumnNames(FilterParams filter)
        {
            string names = string.Empty;

            if (filter.columnRestrict)
            {
                foreach (int colIndex in filter.columnList)
                {
                    if (colIndex < dataGridView.Columns.Count - 2)
                    {
                        if (names.Length > 0)
                        {
                            names += ", ";
                        }
                        names += dataGridView.Columns[2 + colIndex].HeaderText; // skip first two columns: marker + line number
                    }
                }
            }

            return names;
        }

        void ApplyFrozenState(DataGridView gridView)
        {
            SortedDictionary<int, DataGridViewColumn> dict = new SortedDictionary<int, DataGridViewColumn>();
            foreach (DataGridViewColumn col in gridView.Columns)
            {
                dict.Add(col.DisplayIndex, col);
            }
            foreach (DataGridViewColumn col in dict.Values)
            {
                col.Frozen = _freezeStateMap.ContainsKey(gridView) && _freezeStateMap[gridView];
                if (col.Index == _selectedCol)
                {
                    break;
                }
            }
        }

        void ShowTimeSpread(bool show)
        {
            if (show)
            {
                tableLayoutPanel1.ColumnStyles[1].Width = 16;
            }
            else
            {
                tableLayoutPanel1.ColumnStyles[1].Width = 0;
            }
            _timeSpreadCalc.Enabled = show;
        }

        #if DEBUG
        internal void DumpBufferInfo()
        {
            int currentLineNum = dataGridView.CurrentCellAddress.Y;
            CurrentLogFileReader.LogBufferInfoForLine(currentLineNum);
        }

        internal void DumpBufferDiagnostic()
        {
            CurrentLogFileReader.LogBufferDiagnostic();
        }
#endif

        void AddSearchHitHighlightEntry(SearchParams para)
        {
            HilightEntry he = new HilightEntry(para.searchText,
                                  Color.Red, Color.Yellow,
                                  para.isRegex,
                                  para.isCaseSensitive,
                                  false,
                                  false,
                                  false,
                                  false,
                                  null,
                                  true);
            he.IsSearchHit = true;
            lock (_tempHilightEntryListLock)
            {
                _tempHilightEntryList.Add(he);
            }
            RefreshAllGrids();
        }

        void RemoveAllSearchHighlightEntries()
        {
            lock (_tempHilightEntryListLock)
            {
                List<HilightEntry> newList = new List<HilightEntry>();
                foreach (HilightEntry he in _tempHilightEntryList)
                {
                    if (!he.IsSearchHit)
                    {
                        newList.Add(he);
                    }
                }
                _tempHilightEntryList = newList;
            }
            RefreshAllGrids();
        }

        internal void ChangeMultifileMask()
        {
            MultiFileMaskDialog dlg = new MultiFileMaskDialog(this, FileName);
            dlg.Owner = this;
            dlg.MaxDays = _multifileOptions.MaxDayTry;
            dlg.FileNamePattern = _multifileOptions.FormatPattern;
            if (dlg.ShowDialog() == DialogResult.OK)
            {
                _multifileOptions.FormatPattern = dlg.FileNamePattern;
                _multifileOptions.MaxDayTry = dlg.MaxDays;
                if (IsMultiFile)
                {
                    Reload();
                }
            }
        }

        internal void ToggleColumnFinder(bool show, bool setFocus)
        {
            _guiStateArgs.ColumnFinderVisible = show;
            if (show)
            {
                columnComboBox.AutoCompleteMode = AutoCompleteMode.Suggest;
                columnComboBox.AutoCompleteSource = AutoCompleteSource.CustomSource;
                columnComboBox.AutoCompleteCustomSource = new AutoCompleteStringCollection();
                columnComboBox.AutoCompleteCustomSource.AddRange(CurrentColumnizer.GetColumnNames());
                if (setFocus)
                {
                    columnComboBox.Focus();
                }
            }
            else
            {
                dataGridView.Focus();
            }
            tableLayoutPanel1.RowStyles[0].Height = show ? 28 : 0;
        }

        DataGridViewColumn GetColumnByName(DataGridView dataGridView, string name)
        {
            foreach (DataGridViewColumn col in dataGridView.Columns)
            {
                if (col.HeaderText.Equals(name))
                {
                    return col;
                }
            }
            return null;
        }

        void SelectColumn()
        {
            string colName = columnComboBox.SelectedItem as string;
            DataGridViewColumn col = GetColumnByName(dataGridView, colName);
            if (col != null && !col.Frozen)
            {
                dataGridView.FirstDisplayedScrollingColumnIndex = col.Index;
                int currentLine = dataGridView.CurrentCellAddress.Y;
                if (currentLine >= 0)
                {
                    dataGridView.CurrentCell =
                        dataGridView.Rows[dataGridView.CurrentCellAddress.Y].Cells[col.Index];
                }
            }
        }

        void InitPatternWindow()
        {
            _patternWindow = new PatternWindow(this);
            _patternWindow.SetColumnizer(CurrentColumnizer);
            _patternWindow.SetFont(Preferences.fontName, Preferences.fontSize);
            _patternWindow.Fuzzy = _patternArgs.fuzzy;
            _patternWindow.MaxDiff = _patternArgs.maxDiffInBlock;
            _patternWindow.MaxMisses = _patternArgs.maxMisses;
            _patternWindow.Weight = _patternArgs.minWeight;
        }

        void ChangeRowHeight(bool decrease)
        {
            int rowNum = dataGridView.CurrentCellAddress.Y;
            if (rowNum < 0 || rowNum >= dataGridView.RowCount)
            {
                return;
            }
            if (decrease)
            {
                if (!_rowHeightList.ContainsKey(rowNum))
                {
                    return;
                }
                else
                {
                    RowHeightEntry entry = _rowHeightList[rowNum];
                    entry.Height = entry.Height - _lineHeight;
                    if (entry.Height <= _lineHeight)
                    {
                        _rowHeightList.Remove(rowNum);
                    }
                }
            }
            else
            {
                RowHeightEntry entry;
                if (!_rowHeightList.ContainsKey(rowNum))
                {
                    entry = new RowHeightEntry();
                    entry.LineNum = rowNum;
                    entry.Height = _lineHeight;
                    _rowHeightList[rowNum] = entry;
                }
                else
                {
                    entry = _rowHeightList[rowNum];
                }
                entry.Height = entry.Height + _lineHeight;
            }
            dataGridView.UpdateRowHeightInfo(rowNum, false);
            if (rowNum == dataGridView.RowCount - 1 && _guiStateArgs.FollowTail)
            {
                dataGridView.FirstDisplayedScrollingRowIndex = rowNum;
            }
            dataGridView.Refresh();
        }

        int GetRowHeight(int rowNum)
        {
            if (_rowHeightList.ContainsKey(rowNum))
            {
                return _rowHeightList[rowNum].Height;
            }
            else
            {
                return _lineHeight;
            }
        }

        void AddBookmarkAtLineSilently(int lineNum)
        {
            if (!BookmarkProvider.IsBookmarkAtLine(lineNum))
            {
                BookmarkProvider.AddBookmark(new Bookmark(lineNum));
            }
        }

        void AddBookmarkAndEditComment()
        {
            int lineNum = dataGridView.CurrentCellAddress.Y;
            if (!BookmarkProvider.IsBookmarkAtLine(lineNum))
            {
                ToggleBookmark();
            }
            BookmarkComment(BookmarkProvider.GetBookmarkForLine(lineNum));
        }

        void AddBookmarkComment(string text)
        {
            int lineNum = dataGridView.CurrentCellAddress.Y;

            Bookmark bookmark = BookmarkProvider.GetBookmarkForLine(lineNum);

            if (bookmark == null)
            {
                bookmark = new Bookmark(lineNum);
                bookmark.Text = text;
            }
            else
            {
                bookmark.Text += text;
            }

            BookmarkProvider.AddOrUpdateBookmark(bookmark);

            dataGridView.Refresh();
            filterGridView.Refresh();
        }

        void MarkCurrentFilterRange()
        {
            _filterParams.rangeSearchText = filterRangeComboBox.Text;
            ColumnizerCallback callback = new ColumnizerCallback(this);
            RangeFinder rangeFinder = new RangeFinder(_filterParams, callback);
            Range range = rangeFinder.FindRange(dataGridView.CurrentCellAddress.Y);
            if (range != null)
            {
                SetCellSelectionMode(false);
                _noSelectionUpdates = true;
                for (int i = range.StartLine; i <= range.EndLine; ++i)
                {
                    dataGridView.Rows[i].Selected = true;
                }
                _noSelectionUpdates = false;
                UpdateSelectionDisplay();
            }
        }

        void RemoveTempHighlights()
        {
            lock (_tempHilightEntryListLock)
            {
                _tempHilightEntryList.Clear();
            }
            RefreshAllGrids();
        }

        void ToggleHighlightPanel(bool open)
        {
            highlightSplitContainer.Panel2Collapsed = !open;
            toggleHighlightPanelButton.Image = (open ? _panelCloseButtonImage : _panelOpenButtonImage);
        }

        void SetBoomarksForSelectedFilterLines()
        {
            lock (_filterResultList)
            {
                foreach (DataGridViewRow row in filterGridView.SelectedRows)
                {
                    int lineNum = _filterResultList[row.Index];
                    AddBookmarkAtLineSilently(lineNum);
                }
            }
            dataGridView.Refresh();
            filterGridView.Refresh();
        }

        void HandleChangedFilterOnLoadSetting()
        {
            _parentLogTabWin.Preferences.isFilterOnLoad = filterOnLoadCheckBox.Checked;
            _parentLogTabWin.Preferences.isAutoHideFilterList = hideFilterListOnLoadCheckBox.Checked;
            OnFilterListChanged(this);
        }

        void RegisterCancelHandler(BackgroundProcessCancelHandler handler)
        {
            lock (_cancelHandlerList)
            {
                _cancelHandlerList.Add(handler);
            }
        }

        void DeRegisterCancelHandler(BackgroundProcessCancelHandler handler)
        {
            lock (_cancelHandlerList)
            {
                _cancelHandlerList.Remove(handler);
            }
        }

        void FireCancelHandlers()
        {
            lock (_cancelHandlerList)
            {
                foreach (BackgroundProcessCancelHandler handler in _cancelHandlerList)
                {
                    handler.EscapePressed();
                }
            }
        }

        void SyncOtherWindows(DateTime timestamp)
        {
            lock (_timeSyncListLock)
            {
                if (TimeSyncList != null)
                {
                    TimeSyncList.NavigateToTimestamp(timestamp, this);
                }
            }
        }

        void AddSlaveToTimesync(LogWindow slave)
        {
            lock (_timeSyncListLock)
            {
                if (TimeSyncList == null)
                {
                    if (slave.TimeSyncList == null)
                    {
                        TimeSyncList = new TimeSyncList();
                        TimeSyncList.AddWindow(this);
                    }
                    else
                    {
                        TimeSyncList = slave.TimeSyncList;
                    }
                    int currentLineNum = dataGridView.CurrentCellAddress.Y;
                    int refLine = currentLineNum;
                    DateTime timeStamp = GetTimestampForLine(ref refLine, true);
                    if (!timeStamp.Equals(DateTime.MinValue) && !_shouldTimestampDisplaySyncingCancel)
                    {
                        TimeSyncList.CurrentTimestamp = timeStamp;
                    }
                    TimeSyncList.WindowRemoved += TimeSyncList_WindowRemoved;
                }
            }
            slave.AddToTimeSync(this);
            OnSyncModeChanged();
        }

        void FreeSlaveFromTimesync(LogWindow slave)
        {
            slave.FreeFromTimeSync();
        }

        string[] GetColumnsForLine(int lineNumber)
        {
            string[] columns = _columnCache.GetColumnsForLine(CurrentLogFileReader, lineNumber, CurrentColumnizer, ColumnizerCallbackObject);

            return columns;
        }

        protected override string GetPersistString()
        {
            return "LogWindow#" + FileName;
        }



        void LogWindow_Closing(object sender, CancelEventArgs e)
        {
            if (Preferences.askForClose)
            {
                if (MessageBox.Show("Sure to close?", "LogExpert", MessageBoxButtons.YesNo, MessageBoxIcon.Question) ==
                    DialogResult.No)
                {
                    e.Cancel = true;
                    return;
                }
            }
            SavePersistenceData(false);
            CloseLogWindow();
        }



        public delegate void FileSizeChangedEventHandler(object sender, LogEventArgs e);

        public event FileSizeChangedEventHandler FileSizeChanged;

        void OnFileSizeChanged(LogEventArgs e)
        {
            if (FileSizeChanged != null)
            {
                FileSizeChanged(this, e);
            }
        }

        public delegate void StatusLineEventHandler(object sender, StatusLineEventArgs e);

        public event StatusLineEventHandler StatusLineEvent;

        protected void OnStatusLine(StatusLineEventArgs e)
        {
            StatusLineEventHandler handler = StatusLineEvent;
            if (handler != null)
            {
                handler(this, e);
            }
        }

        public delegate void GuiStateEventHandler(object sender, GuiStateArgs e);

        public event GuiStateEventHandler GuiStateUpdate;

        protected void OnGuiState(GuiStateArgs e)
        {
            GuiStateEventHandler handler = GuiStateUpdate;
            if (handler != null)
            {
                handler(this, e);
            }
        }

        public delegate void TailFollowedEventHandler(object sender, EventArgs e);

        public event TailFollowedEventHandler TailFollowed;

        protected void OnTailFollowed(EventArgs e)
        {
            if (TailFollowed != null)
            {
                TailFollowed(this, e);
            }
        }

        public delegate void FileNotFoundEventHandler(object sender, EventArgs e);

        public event FileNotFoundEventHandler FileNotFound;

        protected void OnFileNotFound(EventArgs e)
        {
            if (FileNotFound != null)
            {
                FileNotFound(this, e);
            }
        }

        public delegate void FileRespawnedEventHandler(object sender, EventArgs e);

        public event FileRespawnedEventHandler FileRespawned;

        protected void OnFileRespawned(EventArgs e)
        {
            if (FileRespawned != null)
            {
                FileRespawned(this, e);
            }
        }

        public delegate void FilterListChangedEventHandler(object sender, FilterListChangedEventArgs e);

        public event FilterListChangedEventHandler FilterListChanged;

        protected void OnFilterListChanged(LogWindow source)
        {
            if (FilterListChanged != null)
            {
                FilterListChanged(this, new FilterListChangedEventArgs(source));
            }
        }

        public delegate void CurrentHighlightGroupChangedEventHandler(object sender, CurrentHighlightGroupChangedEventArgs e);

        public event CurrentHighlightGroupChangedEventHandler CurrentHighlightGroupChanged;

        protected void OnCurrentHighlightListChanged()
        {
            if (CurrentHighlightGroupChanged != null)
            {
                CurrentHighlightGroupChanged(this, new CurrentHighlightGroupChangedEventArgs(this, _currentHighlightGroup));
            }
        }

        public delegate void FileReloadFinishedEventHandler(object sender, EventArgs e);

        public event FileReloadFinishedEventHandler FileReloadFinished;

        protected void OnFileReloadFinished()
        {
            if (FileReloadFinished != null)
            {
                FileReloadFinished(this, new EventArgs());
            }
        }

        public delegate void ColumnizerChangedEventHandler(object sender, ColumnizerEventArgs e);

        public event ColumnizerChangedEventHandler ColumnizerChanged;

        void OnColumnizerChanged(ILogLineColumnizer columnizer)
        {
            if (ColumnizerChanged != null)
            {
                ColumnizerChanged(this, new ColumnizerEventArgs(columnizer));
            }
        }

        public delegate void SyncModeChangedEventHandler(object sender, SyncModeEventArgs e);

        public event SyncModeChangedEventHandler SyncModeChanged;

        void OnSyncModeChanged()
        {
            if (SyncModeChanged != null)
            {
                SyncModeChanged(this, new SyncModeEventArgs(IsTimeSynced));
            }
        }



        internal void RefreshAllGrids()
        {
            dataGridView.Refresh();
            filterGridView.Refresh();
        }



        public string GetLogLine(int lineNum)
        {
            return CurrentLogFileReader.GetLogLine(lineNum);
        }

        public Bookmark GetBookmarkForLine(int lineNum)
        {
            return BookmarkProvider.GetBookmarkForLine(lineNum);
        }

        public Font MonospacedFont
        {
            get
            {
                return _fontMonospaced;
            }
        }

        public Font NormalFont
        {
            get
            {
                return _normalFont;
            }
        }

        public Font BoldFont
        {
            get
            {
                return _fontBold;
            }
        }



        public PatternArgs PatternArgs
        {
            get
            {
                return _patternArgs;
            }
            set
            {
                _patternArgs = value;
            }
        }

        public ProgressEventArgs ProgressEventArgs
        {
            get
            {
                return _progressEventArgs;
            }
        }

        public bool IsSearching
        {
            get
            {
                return _isSearching;
            }
            set
            {
                _isSearching = value;
            }
        }

        public bool ShouldCancel
        {
            get
            {
                return _shouldCancel;
            }
            set
            {
                _shouldCancel = value;
            }
        }

        void ILogWindowSearch.SendProgressBarUpdate()
        {
            SendProgressBarUpdate();
        }

        void ILogWindowSearch.UpdateProgressBar(int value)
        {
            UpdateProgressBar(value);
        }

        public PatternWindow PatternWindow
        {
            get
            {
                return _patternWindow;
            }
        }

        public BufferedDataGridView DataGridView
        {
            get
            {
                return dataGridView;
            }
        }

        public int LineCount
        {
            get
            {
                return CurrentLogFileReader.LineCount;
            }
        }

        public LogWindow CurrentLogWindows
        {
            get
            {
                return this;
            }
        }



        public void RefreshLogView()
        {
            RefreshAllGrids();
        }



        // =================== ILogLineColumnizerCallback ============================

        public class LogExpertCallback : ColumnizerCallback, ILogExpertCallback
        {
            public LogExpertCallback(LogWindow logWindow)
                : base(logWindow)
            {
            }

            public void AddTempFileTab(string fileName, string title)
            {
                _logWindow.AddTempFileTab(fileName, title);
            }

            public void AddPipedTab(IList<LineEntry> lineEntryList, string title)
            {
                _logWindow.WritePipeTab(lineEntryList, title);
            }

            public string GetTabTitle()
            {
                return _logWindow.Text;
            }
        }


        protected void OnProgressBarUpdate(ProgressEventArgs e)
        {
            if (ProgressBarUpdate != null)
            {
                ProgressBarUpdate(e);
            }
        }


        //TODO Zarunbal: think about to return directly _guiStateArgs
        public bool IsMultiFile
        {
            get
            {
                return _guiStateArgs.IsMultiFileActive;
            }
            set
            {
                _guiStateArgs.IsMultiFileActive = value;
            }
        }

        public bool IsTempFile { get; protected set; }

        public string ForcedPersistenceFileName { get; set; }

        public Preferences Preferences
        {
            get
            {
                return ConfigManager.Settings.preferences;
            }
        }

        public ILogLineColumnizer CurrentColumnizer
        {
            get
            {
                return _currentColumnizer;
            }
            set
            {
                lock (_currentColumnizerLock)
                {
                    _currentColumnizer = value;
                    Logger.logDebug("Setting columnizer " + _currentColumnizer != null ? _currentColumnizer.GetName() : "<none>");
                }
            }
        }


        public void PreselectColumnizer(string columnizerName)
        {
            ILogLineColumnizer columnizer = Util.FindColumnizerByName(columnizerName, PluginRegistry.GetInstance().RegisteredColumnizers);
            PreSelectColumnizer(Util.CloneColumnizer(columnizer));
        }

        public void Close(bool dontAsk)
        {
            Preferences.askForClose = !dontAsk;
            Close();
        }

        public void LoadFile(string fileName, EncodingOptions encodingOptions)
        {
            LoadFileInternal(fileName, encodingOptions);
        }

        public void LoadFilesAsMulti(string[] fileNames, EncodingOptions encodingOptions)
        {
            LoadFilesAsMultiInternal(fileNames, encodingOptions);
        }


        private void LogEventWorker()
        {
            Thread.CurrentThread.Name = "LogEventWorker";
            while (true)
            {
                Logger.logDebug("Waiting for signal");
                _logEventArgsEvent.WaitOne();
                Logger.logDebug("Wakeup signal received.");
                while (true)
                {
                    LogEventArgs e;
                    int lastLineCount = 0;
                    lock (_logEventArgsList)
                    {
                        Logger.logInfo(string.Format("{0} events in queue", _logEventArgsList.Count));
                        if (_logEventArgsList.Count == 0)
                        {
                            _logEventArgsEvent.Reset();
                            break;
                        }
                        e = _logEventArgsList[0];
                        _logEventArgsList.RemoveAt(0);
                    }
                    if (e.IsRollover)
                    {
                        BookmarkProvider.ShiftBookmarks(e.RolloverOffset);
                        ShiftRowHeightList(e.RolloverOffset);
                        ShiftFilterPipes(e.RolloverOffset);
                        lastLineCount = 0;
                    }
                    else
                    {
                        if (e.LineCount < lastLineCount)
                        {
                            Logger.logError("Line count of event is: " + e.LineCount + ", should be greater than last line count: " + lastLineCount);
                        }
                    }
                    Action<LogEventArgs> callback = new Action<LogEventArgs>(UpdateGrid);
                    Invoke(callback, e);
                    CheckFilterAndHighlight(e);
                    _timeSpreadCalc.SetLineCount(e.LineCount);
                }
            }
        }

        protected void StopLogEventWorkerThread()
        {
            _logEventArgsEvent.Set();
            _logEventHandlerThread.Abort();
            _logEventHandlerThread.Join();
        }


        private void LoadFileInternal(string fileName, EncodingOptions encodingOptions)
        {
            EnterLoadFileStatus();

            if (fileName != null)
            {
                FileName = fileName;
                EncodingOptions = encodingOptions;

                if (CurrentLogFileReader != null)
                {
                    CurrentLogFileReader.StopMonitoringAsync();
                    UnRegisterLogFileReaderEvents();
                }
                if (!LoadPersistenceOptions())
                {
                    if (!IsTempFile)
                    {
                        ILogLineColumnizer columnizer = FindColumnizer();
                        if (columnizer != null)
                        {
                            if (_reloadMemento == null)
                            {
                                columnizer = Util.CloneColumnizer(columnizer);
                            }
                        }
                        PreSelectColumnizer(columnizer);
                    }
                    SetDefaultHighlightGroup();
                }

                // this may be set after loading persistence data
                if (_fileNames != null && IsMultiFile)
                {
                    LoadFilesAsMulti(_fileNames, EncodingOptions);
                    return;
                }
                _columnCache = new ColumnCache();
                try
                {
                    CurrentLogFileReader = new LogfileReader(
                        fileName,
                        EncodingOptions,
                        IsMultiFile,
                        Preferences.bufferCount,
                        Preferences.linesPerBuffer,
                        _multifileOptions);
                    CurrentLogFileReader.UseNewReader = !Preferences.useLegacyReader;
                }
                catch (LogFileException lfe)
                {
                    MessageBox.Show("Cannot load file\n" + lfe.Message, "LogExpert");
                    BeginInvoke(new Action<bool>(Close), new object[] { true });
                    _isLoadError = true;
                    return;
                }

                ILogLineXmlColumnizer xmlColumnizer = CurrentColumnizer as ILogLineXmlColumnizer;

                if (xmlColumnizer != null)
                {
                    CurrentLogFileReader.IsXmlMode = true;
                    CurrentLogFileReader.XmlLogConfig = xmlColumnizer.GetXmlLogConfiguration();
                }

                if (_forcedColumnizerForLoading != null)
                {
                    CurrentColumnizer = _forcedColumnizerForLoading;
                }

                IPreProcessColumnizer preProcessColumnizer = CurrentColumnizer as IPreProcessColumnizer;

                if (CurrentColumnizer is IPreProcessColumnizer)
                {
                    CurrentLogFileReader.PreProcessColumnizer = preProcessColumnizer;
                }
                else
                {
                    CurrentLogFileReader.PreProcessColumnizer = null;
                }

                RegisterLogFileReaderEvents();
                Logger.logInfo("Loading logfile: " + fileName);
                CurrentLogFileReader.startMonitoring();
            }
        }

        private void LoadFilesAsMultiInternal(string[] fileNames, EncodingOptions encodingOptions)
        {
            Logger.logInfo("Loading given files as MultiFile:");

            EnterLoadFileStatus();

            foreach (string name in fileNames)
            {
                Logger.logInfo("File: " + name);
            }

            if (CurrentLogFileReader != null)
            {
                CurrentLogFileReader.stopMonitoring();
                UnRegisterLogFileReaderEvents();
            }

            EncodingOptions = encodingOptions;
            _columnCache = new ColumnCache();

            CurrentLogFileReader = new LogfileReader(
                fileNames,
                EncodingOptions,
                Preferences.bufferCount,
                Preferences.linesPerBuffer,
                _multifileOptions);

            CurrentLogFileReader.UseNewReader = !Preferences.useLegacyReader;
            RegisterLogFileReaderEvents();
            CurrentLogFileReader.startMonitoring();
            FileName = fileNames[fileNames.Length - 1];
            _fileNames = fileNames;
            IsMultiFile = true;
        }

        protected void EnterLoadFileStatusBase()
        {
            Logger.logDebug("EnterLoadFileStatus begin");

            if (InvokeRequired)
            {
                Invoke(new MethodInvoker(EnterLoadFileStatus));
                return;
            }
            _statusEventArgs.StatusText = "Loading file...";
            _statusEventArgs.LineCount = 0;
            _statusEventArgs.FileSize = 0;
            SendStatusLineUpdate();

            _progressEventArgs.MinValue = 0;
            _progressEventArgs.MaxValue = 0;
            _progressEventArgs.Value = 0;
            _progressEventArgs.Visible = true;
            SendProgressBarUpdate();

            _isLoading = true;
            _shouldCancel = true;
            ClearFilterList();
            BookmarkProvider.ClearAllBookmarks();

            Logger.logDebug("EnterLoadFileStatus end");
        }


        protected void ShiftRowHeightList(int offset)
        {
            SortedList<int, RowHeightEntry> newList = new SortedList<int, RowHeightEntry>();
            foreach (RowHeightEntry entry in _rowHeightList.Values)
            {
                int line = entry.LineNum - offset;
                if (line >= 0)
                {
                    entry.LineNum = line;
                    newList.Add(line, entry);
                }
            }
            _rowHeightList = newList;
        }

        protected void ShiftFilterPipes(int offset)
        {
            lock (_filterPipeList)
            {
                foreach (FilterPipe pipe in _filterPipeList)
                {
                    pipe.ShiftLineNums(offset);
                }
            }
        }

        protected void SendStatusLineUpdate()
        {
            _statusLineTrigger.Trigger();
        }

        protected void SendProgressBarUpdate()
        {
            OnProgressBarUpdate(_progressEventArgs);
        }

        protected virtual bool LoadPersistenceOptions()
        {
            if (InvokeRequired)
            {
                return (bool)Invoke(new Func<bool>(LoadPersistenceOptions));
            }

            if (!Preferences.saveSessions && ForcedPersistenceFileName == null)
            {
                return false;
            }

            try
            {
                PersistenceData persistenceData;
                if (ForcedPersistenceFileName == null)
                {
                    persistenceData = Persister.LoadPersistenceDataOptionsOnly(FileName, Preferences);
                }
                else
                {
                    persistenceData = Persister.LoadPersistenceDataOptionsOnlyFromFixedFile(ForcedPersistenceFileName);
                }

                if (persistenceData == null)
                {
                    Logger.logInfo("No persistence data for " + FileName + " found.");
                    return false;
                }

                LoadPersistenceOptions(persistenceData);

                return true;
            }
            catch (Exception ex)
            {
                Logger.logError("Error loading persistence data: " + ex.Message);
                return false;
            }
        }

        protected void PreSelectColumnizer(ILogLineColumnizer columnizer)
        {
            if (columnizer != null)
            {
                CurrentColumnizer = _forcedColumnizerForLoading = columnizer;
            }
            else
            {
                CurrentColumnizer = _forcedColumnizerForLoading = PluginRegistry.GetInstance().RegisteredColumnizers[0];
            }
        }

        /// <summary>
        /// Set an Encoding which shall be used when loading a file. Used before a file is loaded.
        /// </summary>
        /// <param name="encoding"></param>
        protected void SetExplicitEncoding(Encoding encoding)
        {
            EncodingOptions.Encoding = encoding;
        }

        protected ILogLineColumnizer FindColumnizer()
        {
            ILogLineColumnizer columnizer = null;
            string path = Util.GetNameFromPath(FileName);

            if (Preferences.maskPrio)
            {
                columnizer = _parentLogTabWin.FindColumnizerByFileMask(path);
                if (columnizer == null)
                {
                    columnizer = _parentLogTabWin.GetColumnizerHistoryEntry(FileName);
                }
            }
            else
            {
                columnizer = _parentLogTabWin.GetColumnizerHistoryEntry(FileName);
                if (columnizer == null)
                {
                    columnizer = _parentLogTabWin.FindColumnizerByFileMask(path);
                }
            }
            return columnizer;
        }

        protected void SetDefaultHighlightGroup()
        {
            HilightGroup group = _parentLogTabWin.FindHighlightGroupByFileMask(FileName);
            if (group != null)
            {
                SetCurrentHighlightGroup(group.GroupName);
            }
            else
            {
                SetCurrentHighlightGroup("[Default]");
            }
        }

        protected int Search(SearchParams searchParams)
        {
            if (searchParams.searchText == null)
            {
                return -1;
            }

            Action<int> progressFx = new Action<int>(UpdateProgressBar);

            int lineNum = (searchParams.isFromTop && !searchParams.isFindNext) ? 0 : searchParams.currentLine;
            string lowerSearchText = searchParams.searchText.ToLower();
            int count = 0;
            bool hasWrapped = false;
            Regex regex = null;
            string regexPattern = null;
            while (true)
            {
                if ((searchParams.isForward || searchParams.isFindNext) && !searchParams.isShiftF3Pressed)
                {
                    if (lineNum >= CurrentLogFileReader.LineCount)
                    {
                        if (hasWrapped)
                        {
                            StatusLineError("Not found: " + searchParams.searchText);
                            return -1;
                        }
                        lineNum = 0;
                        count = 0;
                        hasWrapped = true;
                        StatusLineError("Started from beginning of file");
                    }
                }
                else
                {
                    if (lineNum < 0)
                    {
                        if (hasWrapped)
                        {
                            StatusLineError("Not found: " + searchParams.searchText);
                            return -1;
                        }
                        count = 0;
                        lineNum = CurrentLogFileReader.LineCount - 1;
                        hasWrapped = true;
                        StatusLineError("Started from end of file");
                    }
                }

                string line = CurrentLogFileReader.GetLogLine(lineNum);

                if (line == null)
                {
                    return -1;
                }

                if (searchParams.isRegex)
                {
                    if (regex == null && string.IsNullOrEmpty(regexPattern) && object.ReferenceEquals(searchParams.searchText, regexPattern))
                    {
                        regex = new Regex(searchParams.searchText, searchParams.isCaseSensitive ? RegexOptions.None : RegexOptions.IgnoreCase);
                    }
                    if (regex.IsMatch(line))
                    {
                        return lineNum;
                    }
                }
                else
                {
                    if (!searchParams.isCaseSensitive)
                    {
                        if (line.ToLower().Contains(lowerSearchText))
                        {
                            return lineNum;
                        }
                    }
                    else
                    {
                        if (line.Contains(searchParams.searchText))
                        {
                            return lineNum;
                        }
                    }
                }

                if ((searchParams.isForward || searchParams.isFindNext) && !searchParams.isShiftF3Pressed)
                {
                    lineNum++;
                }
                else
                {
                    lineNum--;
                }

                if (_shouldCancel)
                {
                    return -1;
                }

                if (++count % PROGRESS_BAR_MODULO == 0)
                {
                    try
                    {
                        if (!Disposing)
                        {
                            Invoke(progressFx, new object[] { count });
                        }
                    }
                    catch (ObjectDisposedException)  // can occur when closing the app while searching
                    {
                    }
                }
            }
        }

        private void button1_Click(object sender, EventArgs e)
        {
            var firstLines = new List<string>();

            using (StreamReader reader = new StreamReader(FileName))
            {
                firstLines.Add(reader.ReadLine());
            }

            File.WriteAllLines(FileName, firstLines.ToArray());
            Reload();
            ClearSelectedView();
        }

        void openInVimToolStripMenuItem_Click(object sender, EventArgs e)
        {
            OpenSelectedRowInVim();
        }

        public void OpenSelectedRowInVim()
        {
            if (dataGridView.SelectedRows.Count != 1)
            {
                return;
            }

            var stackTraceLines = GetFilteredStackTraceForSelectedRow();

            if (stackTraceLines != null && stackTraceLines.Count > 0)
            {
                OutputStackTraceToTempFile(stackTraceLines);
                OpenVim();
            }
        }

        public void OutputStackTraceToTempFile(List<string> stackTraceLines)
        {
            // Output the stack to a temporary file in case the editor is interested in that as well
            var tempFileDir = System.IO.Path.GetTempPath() + "Unity\\";

            if (!Directory.Exists(tempFileDir))
            {
                Directory.CreateDirectory(tempFileDir);
            }

            var tempFilePath = tempFileDir + "logstack.tmp";
            File.WriteAllLines(tempFilePath, stackTraceLines.ToArray());
        }

        public void OpenVim()
        {
            var startInfo = new ProcessStartInfo();

            startInfo.FileName = "C:/Utils/Python34/python.exe";
            startInfo.Arguments = string.Format("C:/Users/Steve/.vim/bundle/vim-config/Ave/Scripts/Python/OpenGvim.py \"{0}\" 1 \"call QuickFixHelper#PopulateQuickFixFromUnityStack()\"", FileName);

            Process.Start(startInfo);
        }

        public List<string> GetFilteredStackTraceForSelectedRow()
        {
            int stacktraceColumn = 5;

            var selectedRow = dataGridView.SelectedRows[0];
            var stackTrace = (string)selectedRow.Cells[stacktraceColumn].Value;

            if (stackTrace == null)
            {
                return null;
            }

            if (stackTrace.Trim() == "")
            {
                return null;
            }

            return Regex.Split(stackTrace, @"/\\").Reverse().Where(ShouldIncludeStackTrace).ToList();
        }

        public bool ShouldIncludeStackTrace(string line)
        {
            bool shouldIgnore = StackTraceIgnoreRegex.IsMatch(line);
            return !shouldIgnore;
        }
    }
}
