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
            ConfigManager cfg = ConfigManager.Instance;
            bool isActive = ConfigManager.Settings.preferences.isWatchDogActive;
            string path = ConfigManager.Settings.preferences.watchDogPath;

            Path = path;
            Filter = "*.log";
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
