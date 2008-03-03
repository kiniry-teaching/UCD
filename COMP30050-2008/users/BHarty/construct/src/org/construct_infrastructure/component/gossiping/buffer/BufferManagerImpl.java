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
package org.construct_infrastructure.component.gossiping.buffer;


import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;
import java.util.Random;
import java.util.SortedMap;
import java.util.TreeMap;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.component.gossiping.Message;
import org.construct_infrastructure.component.gossiping.MessageID;

/**
 * A very simply buffer manager. Messages are not aged as such - when the buffer
 * is full, a random source node is chosen and the message with the lowest
 * sequence number from that node is removed. Recommendation of messages is
 * random.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class BufferManagerImpl extends AbstractConstructComponent implements BufferManager {

   // GRAHAM: *BUG* Sequence numbers eventually wrap!!!

   /**
    * The random number generator used for removing and recommending messages.
    */
   private final Random my_rng;

   /**
    * Artificial limit on the number of entries we're allowed in the buffer.
    */
   private final int my_maxBufferSize;

   /**
    * The number of messages we currently have stored in the buffer.
    */
   private int my_bufferSize;

   /**
    * The object where we store all the messages.
    */
   private final Map my_buffer;

   /**
    * Metadata about messages in the buffer.
    */
   private final Map my_bufferMetadata;

   /**
    * Remember which messages we have already seen. Since we only remove
    * sequence numbers from the lower end of the scale for each host, we simply
    * keep track of the highest sequence number we have removed so far for each
    * message source. Note that this is currently *not scalable* because we
    * never remove sources from the map once they're inserted (over time as new
    * host join and leave, the list will continually increase).
    */
   private final Map my_sourceMetadata;

   /**
    * Create a new buffer manager.
    * 
    * @param some_properties The properties for this component.
    */
   public BufferManagerImpl(final Properties some_properties) {
      super();
      setProperties(some_properties);
      my_rng = new Random();
      my_bufferSize = 0;
      my_maxBufferSize = Integer.parseInt(some_properties.getProperty("buffer_size"));
      my_buffer = new HashMap();
      my_bufferMetadata = new HashMap();
      my_sourceMetadata = new HashMap();
   }

   /**
    * We don't store any metadata for individual messages in this implementation
    * so this method does nothing.
    * 
    * @see org.construct_infrastructure.component.gossiping.buffer.BufferManager#ageMessages()
    */
   public final void ageMessages() {
      // do nothing
   }

   /**
    * Setup links to other components. This implementation of BufferManager does
    * not rely on any other components.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#setupComponentLinks()
    */
   public final void setupComponentLinks() {
      // Empty method
   }

   /**
    * Template method called when the BufferManager is started running.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#onRun()
    */
   public final void onRun() {
      // Empty method
   }

   /**
    * Template method called when the BufferManager is being shutdown.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#onShutdown()
    */
   public void onShutdown() {
      // Empty method
   }

   /**
    * Add a new message to the buffer.
    * 
    * @see org.construct_infrastructure.component.gossiping.buffer.BufferManager#
    *      messageReceived(org.construct_infrastructure.component.gossiping.Message)
    * @param a_message
    *           The message to add.
    * @param some_metadata
    *           Metadata for the message.
    */
   public final void messageReceived(final Message a_message, final Map some_metadata) {
      final MessageID messageID = a_message.getMessageID();
      synchronized (this) {
         // Check that the sequence number is greater than the threshold of
         // messages we have already removed.
         final Integer lastRemoved = (Integer) my_sourceMetadata.get(messageID.getSourceID());
         if (lastRemoved != null && lastRemoved.intValue() >= messageID.getSequenceNumber()) {
            return;
         }

         // Check that we have an entry in the map for this source: create if
         // necessary.
         SortedMap sourceMessageBuffer = (SortedMap) my_buffer.get(messageID.getSourceID());
         if (sourceMessageBuffer == null) {
            sourceMessageBuffer = new TreeMap();
            my_buffer.put(messageID.getSourceID(), sourceMessageBuffer);
         }

         // Check the message isn't already in the buffer.
         if (sourceMessageBuffer.containsKey(new Integer(messageID.getSequenceNumber()))) {
            return;
         }

         // Check that there is a space for the message.
         if (my_bufferSize >= my_maxBufferSize) {
            removeAMessage();
         }

         // Add the message.
         sourceMessageBuffer.put(new Integer(messageID.getSequenceNumber()), a_message);
         my_bufferMetadata.put(messageID, some_metadata);
         my_bufferSize++;
      }
   }

   /**
    * Remove a message to make room in the buffer.
    */
   private void removeAMessage() {
      final int sourceIndex = my_rng.nextInt(my_buffer.size());
      final Map.Entry sourceEntry = (Map.Entry) my_buffer.entrySet().toArray()[sourceIndex];
      final SortedMap source = (SortedMap) sourceEntry.getValue();
      final Message lowest = (Message) source.remove(source.firstKey());
      final MessageID messageID = lowest.getMessageID();
      my_bufferMetadata.remove(messageID);
      if (source.size() == 0) {
         my_buffer.remove(sourceEntry.getKey());
      }
      my_sourceMetadata.put(messageID.getSourceID(),
            new Integer(messageID.getSequenceNumber()));
      my_bufferSize--;
   }

   /**
    * Get a summary of messages in the buffer. Summaries consist of message
    * source id's and sequence numbers.
    * 
    * @see org.construct_infrastructure.component.gossiping.buffer.BufferManager#getSummary()
    * @return A summary of the buffer.
    */
   public final Summary getSummary() {
      final Summary summary = new Summary();
      synchronized (this) {
         final Iterator sourceIterator = my_buffer.values().iterator();
         while (sourceIterator.hasNext()) {
            final SortedMap currentEntry = (SortedMap) sourceIterator.next();
            final Iterator messageIterator = currentEntry.values().iterator();
            while (messageIterator.hasNext()) {
               final Message current = (Message) messageIterator.next();
               summary.add(current.getMessageID());
            }
         }
      }
      return summary;
   }

   /**
    * Determine whether the buffer currently contains a given message.
    * 
    * @see org.construct_infrastructure.component.gossiping.buffer.BufferManager#
    *      contains(org.construct_infrastructure.component.gossiping.MessageID)
    * @param an_id
    *           The ID of the message in question.
    * @return True if the buffer contains the message.
    */
   public final boolean contains(final MessageID an_id) {
      return (get(an_id) != null);
   }

   /**
    * Get a particular message from the buffer.
    * 
    * @see org.construct_infrastructure.component.gossiping.buffer.BufferManager#
    *      get(org.construct_infrastructure.component.gossiping.MessageID)
    * @param an_id
    *           The ID of the message to retrieve.
    * @return The message or null if it does not exist.
    */
   public final Message get(final MessageID an_id) {
      final SortedMap sourceBuffer = (SortedMap) my_buffer.get(an_id.getSourceID());
      if (sourceBuffer == null) {
         return null;
      }
      return (Message) sourceBuffer.get(new Integer(an_id.getSequenceNumber()));
   }

   /**
    * Get metadata about a particular message from the buffer.
    * 
    * @see org.construct_infrastructure.component.gossiping.buffer.BufferManager#
    *      getMetadata(org.construct_infrastructure.component.gossiping.MessageID)
    * @param an_id
    *           The ID of the message metadata to retrieve.
    * @return The metadata Map or null if it does not exist.
    */
   public final Map getMetadata(final MessageID an_id) {
      return (Map) my_bufferMetadata.get(an_id);
   }

   /**
    * Compare the given summary with the messages in this buffer and recommend a
    * message to request.
    * 
    * @see org.construct_infrastructure.component.gossiping.buffer.BufferManager#
    *      recommendMessage(org.construct_infrastructure.component.gossiping.buffer.Summary)
    * @param a_summary
    *           The summary to compare with this buffer.
    * @return A message ID to request or null if all the messages are already
    *         present in the buffer.
    */
   public final MessageID recommendMessage(final Summary a_summary) {
      MessageID messageID = null;
      a_summary.subtract(getSummary());
      if (a_summary.isEmpty()) {
         return null;
      }

      int selected = my_rng.nextInt(a_summary.size());
      final Iterator iterator = a_summary.iterator();
      while (iterator.hasNext() && selected >= 0) {
         messageID = (MessageID) iterator.next();
         selected--;
      }

      return messageID;
   }

}
