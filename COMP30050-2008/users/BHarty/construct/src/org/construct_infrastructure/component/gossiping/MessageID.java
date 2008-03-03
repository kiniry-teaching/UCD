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

import java.io.IOException;

import org.construct_infrastructure.component.gossiping.util.DataTransformer;
import org.construct_infrastructure.component.gossiping.util.StuffedByteArrayIterator;
import org.construct_infrastructure.component.gossiping.util.StuffedByteArrayOutputStream;
import org.construct_infrastructure.component.gossiping.util.TransformationException;


/**
 * A message ID uniquely identifies a message by the source and a sequence
 * number.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class MessageID {

   /**
    * A weak source ID used to identify this source of messages from this
    * process.
    */
   private static String theSourceID;

   /**
    * Keeps track of the number of messages created.
    */
   private static int currentSequenceNumber;

   /**
    * A unique ID which identifies the source of this message.
    */
   private String my_sourceID;

   /**
    * The sequence number of this message.
    */
   private int my_sequenceNumber;

   /**
    * This message ID serialized to a byte stream.
    */
   private final byte[] my_serializedData;

   /**
    * Create a new message ID using the generated source ID of this process and
    * a sequence number.
    * 
    * @throws TransformationException
    *            If this message ID could not be serialized.
    */
   public MessageID() throws TransformationException {
      super();
      my_sourceID = getTheSourceID();
      my_sequenceNumber = currentSequenceNumber++;
      my_serializedData = doSerialize();
   }

   /**
    * Create a message ID using the serialized data contained in the given
    * array.
    * 
    * @param some_serializedData
    *           The bytes representing a message ID.
    * @throws TransformationException
    *            If this message ID could not be deserialized.
    * @throws NullPointerException
    *            If some_serializedData is null.
    */
   public MessageID(final byte[] some_serializedData) throws TransformationException,
         NullPointerException {
      super();
      my_serializedData = (byte[]) some_serializedData.clone();
      deserialize(DataTransformer.decompressBytes(my_serializedData));
   }

   /**
    * Perform the serialization of this message ID to a byte array.
    * 
    * @return This message ID serialized to a byte array.
    * @throws TransformationException
    *            If this message ID could not be serialized.
    */
   private byte[] doSerialize() throws TransformationException {
      final byte[] sourceIDAsBytes = my_sourceID.getBytes();
      final byte[] sequenceNumberAsBytes = Integer.toString(my_sequenceNumber).getBytes();

      final StuffedByteArrayOutputStream combinedStream = new StuffedByteArrayOutputStream();
      combinedStream.writeSection(sourceIDAsBytes);
      combinedStream.writeSection(sequenceNumberAsBytes);
      return DataTransformer.compressBytes(combinedStream.toByteArray());
   }

   /**
    * Deserialize the uncompressed byte array into the jena model and metadata
    * model.
    * 
    * @param some_uncompressedBytes
    *           The byte array to deserialize.
    * @throws TransformationException
    *            If this message could not be deserialized.
    */
   private void deserialize(final byte[] some_uncompressedBytes)
      throws TransformationException {
      try {
         final StuffedByteArrayIterator iterator = new StuffedByteArrayIterator(
               some_uncompressedBytes);
         my_sourceID = new String(iterator.nextSection());
         my_sequenceNumber = Integer.parseInt(new String(iterator.nextSection()));
      } catch (IOException e) {
         throw new TransformationException("Unexpected end of message!", e);
      } catch (NumberFormatException e) {
         throw new TransformationException("Unable to deserialise illegal message format.", e);
      }
   }

   /**
    * Generate a source ID. Generated from the time, hostname and username.
    * 
    * @return A source ID.
    */
   private static synchronized String getTheSourceID() {
      // GRAHAM: Find a better way of generating a unique source ID
      if (theSourceID == null) {
         theSourceID = System.getProperty("user.name") + System.getProperty("host.name")
               + System.currentTimeMillis();
      }
      return theSourceID;
   }

   /**
    * Get a unique ID which identifies the source of this message.
    * 
    * @see org.construct_infrastructure.component.gossiping.Message#getSourceID()
    * @return The source ID.
    */
   public final String getSourceID() {
      return my_sourceID;
   }

   /**
    * Get the sequence number associated with this message.
    * 
    * @see org.construct_infrastructure.component.gossiping.Message#getSequenceNumber()
    * @return The sequence number.
    */
   public final int getSequenceNumber() {
      return my_sequenceNumber;
   }

   /**
    * Return the contents of this message ID in byte array form.
    * 
    * @return This message ID serialized as a byte array.
    */
   public final byte[] serialize() {
      return (byte[]) my_serializedData.clone();
   }

   /**
    * Test if this message ID is equal to the given object.
    * 
    * @see java.lang.Object#equals(java.lang.Object)
    * @param a_messageID
    *           The object to compare with.
    * @return True if the objects represent the same message ID.
    */
   public final boolean equals(final Object a_messageID) {
      // GRAHAM: Consider rewriting to avoid the PMD warning.
      if (!(a_messageID instanceof MessageID)) {
         return false;
      }
      final MessageID other = (MessageID) a_messageID;
      return my_sourceID.equals(other.my_sourceID)
            && (my_sequenceNumber == other.my_sequenceNumber);
   }

   /**
    * Generate the hashcode for this message ID.
    * 
    * @see java.lang.Object#hashCode()
    * @return The hashcode for this message ID.
    */
   public final int hashCode() {
      return my_sourceID.hashCode() + my_sequenceNumber;
   }

   /**
    * Generate a textual representation of this message ID.
    * 
    * @see java.lang.Object#toString()
    * @return A textual description of this ID.
    */
   public final String toString() {
      return my_sourceID + "[" + my_sequenceNumber + "]";
   }
}
