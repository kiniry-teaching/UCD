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
package org.construct_infrastructure.component.gossiping;


import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.locks.ReentrantLock;

import org.construct_infrastructure.component.gossiping.util.TransformationException;

/**
 * Implements a simple message queue which aggregates messages over a short
 * period of time into a single large message before notifying the gossip
 * manager.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class MessageQueue extends Timer {

   /**
    * The threshold for the size of a single message before a new message is
    * forced to be sent.
    */
   private static final int THRESHOLD = 30000;

   /**
    * The frequency of updates sent to the gossip manager in milliseconds.
    */
   private static final int UPDATE_PERIOD = 1000;

   /**
    * The gossip manager that owns this message queue and will be notified when
    * messages must be delivered.
    */
   private final GossipManagerImpl my_owner;

   /**
    * Lock that synchronises access to the statement and metadata buffers.
    */
   private final ReentrantLock my_lock;

   /**
    * The buffer that holds the statements being queued.
    */
   private StringBuffer my_statements;

   /**
    * The buffer that holds the metadata being queued.
    */
   private StringBuffer my_metadata;

   /**
    * Indicates if this timer has been cancelled.
    */
   private boolean my_timerCanceled;

   /**
    * The timer task which periodically delivers all messages in the buffer to
    * the gossip manager.
    */
   private DeliveryTask my_deliveryTask;

   /**
    * Create a new message queue which will notify the given gossip manager.
    * 
    * @param the_owner
    *           The gossip manager who owns this queue.
    */
   public MessageQueue(final GossipManagerImpl the_owner) {
      super();
      my_owner = the_owner;
      my_lock = new ReentrantLock();
      my_statements = new StringBuffer();
      my_metadata = new StringBuffer();
      my_timerCanceled = false;
   }

   /**
    * Schedule the message delivery to the gossiping layer.
    */
   public final void scheduleUpdates() {
      try {
         my_lock.lock();
         if (my_owner != null && !my_timerCanceled) {
            my_deliveryTask = new DeliveryTask();
            schedule(my_deliveryTask, 0, UPDATE_PERIOD);
         }
      } finally {
         my_lock.unlock();
      }

   }

   /**
    * Cancels any running tasks.
    */
   public final void cancel() {
      try {
         my_lock.lock();
         if (my_deliveryTask != null && !my_timerCanceled) {
            my_deliveryTask.cancel();
         }
         my_timerCanceled = true;
      } finally {
         my_lock.unlock();
      }
      super.cancel();
   }

   /**
    * Add data to the queue.
    * 
    * @param some_statements
    *           The statements to add to the queue.
    * @param some_metadata
    *           The metadata to add to the queue.
    */
   public final void addToQueue(final String some_statements, final String some_metadata) {
      try {
         my_lock.lock();
         my_statements.append(some_statements);
         my_metadata.append(some_metadata);
         if (my_statements.length() > THRESHOLD) {
            sendMessage();
         }
      } finally {
         my_lock.unlock();
      }
   }

   /**
    * Create a message from the buffers and pass it to the gossiping layer.
    */
   private void sendMessage() {
      try {
         my_owner.gossipMessage(new StringMessage(my_statements.toString(), my_metadata
               .toString()));
      } catch (TransformationException e) {
         my_owner.getLogger().warning("Unable to serialize statemens for gossiping!");
      }

      my_statements = new StringBuffer();
      my_metadata = new StringBuffer();
   }

   /**
    * This task executes periodically to delivery the messages that are held in
    * the buffer.
    * 
    * @author Graham Williamson (graham.williamson@ucd.ie)
    */
   public class DeliveryTask extends TimerTask {

      /**
       * @inheritDoc
       * @see java.util.TimerTask#run()
       */
      public final void run() {
         try {
            my_lock.lock();
            if (!my_timerCanceled && (my_statements.length() != 0)) {
               sendMessage();
            }
         } finally {
            my_lock.unlock();
         }
      }

   }

}
