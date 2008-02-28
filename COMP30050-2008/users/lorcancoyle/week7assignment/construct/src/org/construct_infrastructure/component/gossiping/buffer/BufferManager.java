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

import java.util.Map;

import org.construct_infrastructure.component.ConstructComponent;
import org.construct_infrastructure.component.gossiping.Message;
import org.construct_infrastructure.component.gossiping.MessageID;


/**
 * The BufferManager is responsible for maintaining a buffer of messages and
 * associated metadata.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public interface BufferManager extends ConstructComponent {

   /**
    * Age the messages in the buffer. This is invoked on each round of gossiping
    * to allow age based removal of messages.
    */
   void ageMessages();

   /**
    * Notify the buffer manager that a message has been received.
    * 
    * @param a_message
    *           The received message.
    * @param some_metadata
    *           Metadata for the message.
    */
   void messageReceived(Message a_message, Map some_metadata);

   // messageReceived: Check we haven't already got it in the buffer (or already
   // *had* and discarded it!) then add it. If it's already there, we can store
   // various metadata: when did we last receive a message about it? how many
   // times have we receive this message? Perhaps it would be interesting to
   // also maintain metadata about what messages our peers have: we would have
   // to do that via the summaries though (we could possibly delegate the
   // comparison of summaries and the selection of which messages to request to
   // the buffer manager, allowing it to look at the summaries when they arrive)
   // so we would know, say, how popular a given message is amongst our peers
   // and that could be used as a criteron for selecting messages to discard.
   // This may also touch on some of the work with classifying messages
   // semantically: we may be able to identify how popular particular topics are
   // with the peers currently in our membership list...or something. ;)

   /**
    * Get a summary of messages in the buffer. Summaries consist of message
    * source id's and sequence numbers.
    * 
    * @return A summary of the buffer.
    */
   Summary getSummary();

   /**
    * Determine whether the buffer currently contains a given message.
    * 
    * @param an_id
    *           The ID of the message in question.
    * @return True if the buffer contains the message.
    */
   boolean contains(MessageID an_id);

   /**
    * Get a particular message from the buffer.
    * 
    * @param an_id
    *           The ID of the message to retrieve.
    * @return The message or null if it does not exist.
    */
   Message get(MessageID an_id);

   /**
    * Get metadata about a particular message from the buffer.
    * 
    * @param an_id
    *           The ID of the message metadata to retrieve.
    * @return The metadata Map or null if it does not exist.
    */
   Map getMetadata(final MessageID an_id);
   
   /**
    * Compare the given summary with the messages in this buffer and recommend a
    * message to request.
    * 
    * @param a_summary
    *           The summary to compare with this buffer.
    * @return A message ID to request or null if all the messages are already
    *         present in the buffer.
    */
   MessageID recommendMessage(Summary a_summary);
   // GRAHAM: Extend so it's possible to request more than one message per
   // summary received. Do we really want to do this? How do we decide how many
   // to request? Gah. Perhaps we request as many as we can and leave it up the
   // receiving node to decide how many to send us? Or maybe we request up to N
   // messages (again, the receiving nopde and decide not to send us some if it
   // doesn't want to!).

   // recommendMessage: when we recommend a message we can record that in the
   // metadata associated with each message ID in the buffer (we would also have
   // to record whether the actual message is present in the buffer for each
   // message ID as well) and in this way we can use the number of times it has
   // been requested as a guide when requesting a message the next time (i.e. if
   // a message was recently requested the reply may be en route so we should
   // request another to avoid duplicates). The message requested metadata flag
   // could be cleared after a certain number of rounds (even just one to
   // prevent the same message being requested multiple times in a single round)
   // by using the ageMessages() method.
}
