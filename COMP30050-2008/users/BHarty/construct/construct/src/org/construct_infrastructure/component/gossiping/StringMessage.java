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
 * A message capable of being disseminated by the gossiping subsystem which
 * contains data from construct.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class StringMessage implements Message {

   /**
    * The model stored in this message.
    */
   private String my_model;

   /**
    * The metadata stored in this message.
    */
   private String my_metadata;

   /**
    * The message ID of this message.
    */
   private MessageID my_messageID;

   /**
    * The time that this message was created.
    */
   private long my_time;

   /**
    * The serialized version of the data stored in this message.
    */
   private final byte[] my_serializedData;

   /**
    * Create a new message containing data from the given model and metadata
    * model.
    * 
    * @param a_model
    *           The model to store in this message.
    * @param some_metadata
    *           The metadata to store in this message.
    * @throws TransformationException
    *            If this message could not be serialized.
    * @throws NullPointerException
    *            If either parameter is null.
    */
   public StringMessage(final String a_model, final String some_metadata)
      throws TransformationException, NullPointerException {
      super();
      my_model = a_model;
      my_metadata = some_metadata;
      my_messageID = new MessageID();
      my_time = System.currentTimeMillis();
      my_serializedData = doSerialize();
   }

   /**
    * Create a new message from the serialized data obtained from another
    * message.
    * 
    * @param some_serializedData
    *           The serialized data to build this message from.
    * @throws TransformationException
    *            If this message could not be deserialized.
    * @throws NullPointerException
    *            If some_serializedData is null.
    */
   public StringMessage(final byte[] some_serializedData) throws TransformationException,
         NullPointerException {
      super();
      my_serializedData = (byte[]) some_serializedData.clone();
      deserialize(DataTransformer.decompressBytes(my_serializedData));
   }

   /**
    * Get the model stored in this message.
    * 
    * @return Returns the model.
    */
   public final String getModel() {
      return my_model;
   }

   /**
    * Get the metadata stored in this message.
    * 
    * @return Returns the metadata.
    */
   public final String getMetadata() {
      return my_metadata;
   }

   /**
    * Get the message ID of this message.
    * 
    * @see org.construct_infrastructure.component.gossiping.Message#getMessageID()
    * @return The message ID of this message.
    */
   public final MessageID getMessageID() {
      return my_messageID;
   }

   /**
    * Get the time that this message was created.
    * 
    * @see org.construct_infrastructure.component.gossiping.Message#getTime()
    * @return The time this message was created.
    */
   public final long getTime() {
      return my_time;
   }

   /**
    * Return the contents of this message in byte array form.
    * 
    * @see org.construct_infrastructure.component.gossiping.Message#serialize()
    * @return This message as a byte array.
    */
   public final byte[] serialize() {
      return (byte[]) my_serializedData.clone();
   }

   /**
    * Perform the serialization of this message.
    * 
    * @return This message serialized as a compressed byte array.
    * @throws TransformationException
    *            If this message could not be serialized.
    * @throws NullPointerException
    *            If my_messageID, my_model, or my_metadata are null.
    */
   private byte[] doSerialize() throws TransformationException, NullPointerException {
      final byte[] messageIDAsBytes = my_messageID.serialize();
      final byte[] timeAsBytes = Long.toString(my_time).getBytes();
      final byte[] modelAsBytes = my_model.getBytes();
      final byte[] metadataAsBytes = my_metadata.getBytes();

      final StuffedByteArrayOutputStream combinedStream = new StuffedByteArrayOutputStream();
      combinedStream.writeSection(messageIDAsBytes);
      combinedStream.writeSection(timeAsBytes);
      combinedStream.writeSection(modelAsBytes);
      combinedStream.writeSection(metadataAsBytes);
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
         my_messageID = new MessageID(iterator.nextSection());
         my_time = Long.parseLong(new String(iterator.nextSection()));
         my_model = new String(iterator.nextSection());
         my_metadata = new String(iterator.nextSection());
      } catch (IOException e) {
         throw new TransformationException("Unexpected end of message!", e);
      } catch (NumberFormatException e) {
         throw new TransformationException("Unable to deserialise illegal message format.", e);
      }
   }

   /**
    * Test if this message is equal to the given object.
    * 
    * @see java.lang.Object#equals(java.lang.Object)
    * @param a_message
    *           The object to compare with.
    * @return True if the objects represent the same message.
    */
   public final boolean equals(final Object a_message) {
      // GRAHAM: Consider rewriting to avoid the PMD warning.
      if (!(a_message instanceof StringMessage)) {
         return false;
      }
      final StringMessage other = (StringMessage) a_message;
      return my_messageID.equals(other.my_messageID) && my_model.equals(other.my_model)
            && my_metadata.equals(other.my_metadata) && (my_time == other.my_time);
   }

   /**
    * Get a hashcode for this string message.
    * 
    * @see java.lang.Object#hashCode()
    * @return A hashcode for this string message.
    */
   public final int hashCode() {
      return my_messageID.hashCode() + my_model.hashCode() + my_metadata.hashCode()
            + (int) my_time;
   }

   /**
    * Get this StringMessage formatted as a single String.
    * 
    * @return This StringMessage formatted as a single String.
    * @see java.lang.Object#toString()
    */
   public final String toString() {
      final StringBuffer buffer = new StringBuffer();
      buffer.append("Model: ");
      buffer.append(my_model);
      buffer.append("\nMetadata: ");
      buffer.append(my_metadata);
      buffer.append("\nMsgID: ");
      buffer.append(my_messageID);
      buffer.append("\nTime");
      buffer.append(my_time);
      buffer.append("\n");
      return buffer.toString();
   }
}
