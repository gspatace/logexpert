﻿using System;
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
            Path = ConfigManager.Settings.preferences.watchDogPath;
            Filter = ConfigManager.Settings.preferences.watchDogPattern;
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
