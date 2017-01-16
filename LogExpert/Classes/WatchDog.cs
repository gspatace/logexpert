using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;

namespace LogExpert.Classes
{
    public class WatchDog : FileSystemWatcher
    {
        public WatchDog()
        {
            string path = ConfigManager.Settings.preferences.watchDogPath;
            string filter = ConfigManager.Settings.preferences.watchDogPattern;

            Path = path;
            Filter = filter;
            NotifyFilter = NotifyFilters.LastAccess | NotifyFilters.LastWrite | NotifyFilters.FileName | NotifyFilters.DirectoryName;
            Created += new FileSystemEventHandler(OnChanged);
        }

        // Define the event handlers.
        private void OnChanged(object source, FileSystemEventArgs e)
        {
            OnNewFile(e);
        }

        public event EventHandler<FileSystemEventArgs> NewFile;

        protected virtual void OnNewFile(FileSystemEventArgs ea)
        {
            if( NewFile != null)
            {
                NewFile(this, ea);
            }
        }
    }
}
