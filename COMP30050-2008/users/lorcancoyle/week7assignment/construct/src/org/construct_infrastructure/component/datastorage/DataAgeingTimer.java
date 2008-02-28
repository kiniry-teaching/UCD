//
// $Revision: 7373 $: $Date: 2008-01-24 11:20:18 +0000 (Thu, 24 Jan 2008) $ - $Author: gstevenson $
//
//  This file is part of Construct, a context-aware systems platform.
//  Copyright (c) 2006, 2007, 2008 UCD Dublin. All rights reserved.
// 
//  Construct is free software; you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as
//  published by the Free Software Foundation; either version 2.1 of
//  the License, or (at your option) any later version.
// 
//  Construct is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
//  GNU Lesser General Public License for more details.
// 
//  You should have received a copy of the GNU Lesser General Public
//  License along with Construct; if not, write to the Free Software
//  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
//  USA
//
//  Further information about Construct can be obtained from
//  http://www.construct-infrastructure.org
package org.construct_infrastructure.component.datastorage;

import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.locks.ReentrantLock;

/**
 * This class controls the timing of the execution of the enclosed data ageing maintenance
 * task.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class DataAgeingTimer extends Timer {

   /**
    * The repeat period for the timed task in ms.
    */
   private static final int REPEAT_PERIOD = 10000;

   /**
    * The task to apply to the data store manager.
    */
   private DataAgeingTask my_ageingTask;

   /**
    * Lock to prevent task executing during shutdown.
    */
   private final ReentrantLock my_lock;

   /**
    * Has the timer been canceled?
    */
   private boolean my_timerCanceled;

   /**
    * The data store manager associated with this timer.
    */
   private final transient DataStoreManager my_dataStoreManager;

   /**
    * Creates a new data ageing timer that will operate on the given data store manager.
    * 
    * @param the_dataStoreManager
    *           the data store manager on which to operate
    */
   public DataAgeingTimer(final DataStoreManagerImpl the_dataStoreManager) {
      super();
      my_lock = new ReentrantLock();
      my_dataStoreManager = the_dataStoreManager;
      my_timerCanceled = false;
   }

   /**
    * Schedule the updates to the data store.
    */
   public void scheduleUpdates() {
      try {
         my_lock.lock();
         if (my_dataStoreManager != null && !my_timerCanceled) {
            my_ageingTask = new DataAgeingTask();
            schedule(my_ageingTask, 0, REPEAT_PERIOD);
         }
      } finally {
         my_lock.unlock();
      }

   }

   /**
    * Cancels any running tasks.
    */
   public void cancel() {
      try {
         my_lock.lock();
         if (my_ageingTask != null && !my_timerCanceled) {
            my_ageingTask.cancel();
         }
         my_timerCanceled = true;
      } finally {
         my_lock.unlock();
      }
      super.cancel();
   }

   /**
    * When called, the DataAgeingTask class calls the method on the data store manager that
    * checks for and removes old data.
    * 
    * @author Graeme Stevenson
    */
   private class DataAgeingTask extends TimerTask {

      /**
       * Calls the method on the data store manager that checks for and removes old data.
       */
      public void run() {
         try {
            my_lock.lock();
            if (!my_timerCanceled) {
               my_dataStoreManager.removeAllExpiredStatements();
            }
         } finally {
            my_lock.unlock();
         }
      }
   }
}
