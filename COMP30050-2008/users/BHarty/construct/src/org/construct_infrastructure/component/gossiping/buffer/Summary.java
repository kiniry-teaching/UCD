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


import java.io.IOException;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.construct_infrastructure.component.gossiping.MessageID;
import org.construct_infrastructure.component.gossiping.util.StuffedByteArrayIterator;
import org.construct_infrastructure.component.gossiping.util.StuffedByteArrayOutputStream;
import org.construct_infrastructure.component.gossiping.util.TransformationException;

/**
 * A summary of the contents of the message buffer. A summary consists of the
 * message ID's belonging to the messages in the buffer.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class Summary {

   // GRAHAM: Perhaps a summary should also contain the 'age' of the messages.
   // The summary should be easily altered to include specific data required by
   // a particular buffer manager. E.g. how many rounds have they been gossiped
   // for? how many hosts has the message traversed to get here?

   /**
    * The set of message ID's that backs this summary.
    */
   private final Set my_messageIDSet;

   /**
    * Create a new, empty summary.
    */
   public Summary() {
      my_messageIDSet = Collections.synchronizedSet(new HashSet());
   }

   /**
    * Create a summary from the given raw summary data.
    * 
    * @param some_rawSummaryData
    *           The raw bytes representing a summary.
    * @throws TransformationException
    *            If the summary could not be deserialized.
    * @throws IllegalArgumentException
    *            If some_rawSummaryData is null.
    */
   public Summary(final byte[] some_rawSummaryData) throws TransformationException,
         IllegalArgumentException {
      super();
      if (some_rawSummaryData == null) {
         throw new IllegalArgumentException();
      }
      my_messageIDSet = deserialize(some_rawSummaryData);
   }

   /**
    * Add a message ID to the summary.
    * 
    * @param a_messageID
    *           The message ID to add.
    * @throws IllegalArgumentException
    *            If a_messageID is null.
    */
   public final void add(final MessageID a_messageID) throws IllegalArgumentException {
      if (a_messageID == null) {
         throw new IllegalArgumentException();
      }
      my_messageIDSet.add(a_messageID);
   }

   /**
    * Check if this summary contains a given message ID.
    * 
    * @param a_messageID
    *           The message ID to check for.
    * @return True if the summary contains the message ID.
    * @throws IllegalArgumentException
    *            If a_message is null.
    */
   public final boolean contains(final MessageID a_messageID) throws IllegalArgumentException {
      if (a_messageID == null) {
         throw new IllegalArgumentException();
      }
      return my_messageIDSet.contains(a_messageID);
   }

   /**
    * Get an iterator over the set of message ID's in this summary.
    * 
    * @return An iterator over the set of message ID's in this summary.
    */
   public final Iterator iterator() {
      return my_messageIDSet.iterator();
   }

   /**
    * Remove a message ID from this summary.
    * 
    * @param a_messageID
    *           The message ID to remove.
    * @return True if the summary contained the message ID.
    * @throws IllegalArgumentException
    *            If a_message is null.
    */
   public final boolean remove(final MessageID a_messageID) throws IllegalArgumentException {
      if (a_messageID == null) {
         throw new IllegalArgumentException();
      }
      return my_messageIDSet.remove(a_messageID);
   }

   /**
    * Get the number of messages in this summary.
    * 
    * @return The number of messages in this summary.
    */
   public final int size() {
      return my_messageIDSet.size();
   }

   /**
    * Check if this summary has no messages in it.
    * 
    * @return True if the summary represents an empty message buffer.
    */
   public final boolean isEmpty() {
      return my_messageIDSet.isEmpty();
   }

   /**
    * Remove all the message ID's that appear in the given summary from this
    * summary.
    * 
    * @param a_summary
    *           The summary to subtract.
    * @return True if this summary changed as a result of this method
    *         invocation.
    */
   public final boolean subtract(final Summary a_summary) {
      return my_messageIDSet.removeAll(a_summary.my_messageIDSet);
   }

   /**
    * Serialize this summary to a string of bytes.
    * 
    * @return The summary represented as a series of bytes.
    */
   public final byte[] serialize() {
      final StuffedByteArrayOutputStream combinedStream = new StuffedByteArrayOutputStream();
      final Iterator iterator = my_messageIDSet.iterator();
      MessageID currentID;
      while (iterator.hasNext()) {
         currentID = (MessageID) iterator.next();
         combinedStream.writeSection(currentID.serialize());
      }
      return combinedStream.toByteArray();
   }

   /**
    * Deserialize a summary from a string of raw bytes.
    * 
    * @param some_rawSummaryData
    *           The raw bytes to deserialize.
    * @return The set represented by the raw data.
    * @throws TransformationException
    *            If the summary could not be deserialized.
    */
   private Set deserialize(final byte[] some_rawSummaryData) throws TransformationException {
      final Set idList = Collections.synchronizedSet(new HashSet());
      final StuffedByteArrayIterator iterator = new StuffedByteArrayIterator(
            some_rawSummaryData);
      try {
         while (iterator.hasAnotherSection()) {
            idList.add(new MessageID(iterator.nextSection()));
         }
      } catch (IOException e) {
         throw new TransformationException("Unexpected end of message!");
      }
      return idList;
   }

   /**
    * Determine if this summary is equal to the given object.
    * 
    * @see java.lang.Object#equals(java.lang.Object)
    * @param a_summary
    *           The object to compare with.
    * @return True if the objects represent an equivalent summary.
    */
   public final boolean equals(final Object a_summary) {
      // GRAHAM: Consider rewriting to avoid PMD warning.
      if (!(a_summary instanceof Summary)) {
         return false;
      }
      final Summary summary = (Summary) a_summary;
      return my_messageIDSet.equals(summary.my_messageIDSet);
   }

   /**
    * Generate the hashcode for this summary.
    * 
    * @see java.lang.Object#hashCode()
    * @return The hashcode for this summary.
    */
   public final int hashCode() {
      return my_messageIDSet.hashCode();
   }

   /**
    * Generate a string representation of this summary.
    * 
    * @see java.lang.Object#toString()
    * @return A string representation of this summary.
    */
   public final String toString() {
      final StringBuffer buffer = new StringBuffer();
      buffer.append("Summary:\n");
      final Iterator iterator = my_messageIDSet.iterator();
      while (iterator.hasNext()) {
         buffer.append(" -> " + iterator.next() + "\n");
      }
      return buffer.toString();
   }

}
