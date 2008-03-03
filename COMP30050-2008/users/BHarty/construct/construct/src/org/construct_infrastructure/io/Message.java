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
package org.construct_infrastructure.io;


/**
 * This class represents a Construct Message with three components: a message ID, a length, and
 * a payload.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public class Message {

   /**
    * The number of chars in a query ID.
    */
   private static final int QUERY_ID_LENGTH = 40;

   /**
    * The message id.
    */
   private final String my_id;

   /**
    * The payload of the message.
    */
   private final String my_payload;

   /**
    * Creates a new message object.
    * @param the_id the id of the message.
    * @param the_payload the payload of the message.
    */
   public Message(final String the_id, final String the_payload) {
      my_id = the_id;
      my_payload = the_payload;
   }

   /**
    * Is this message related to a query?
    * 
    * @return true if the message is a [query|query response|query unsubscribe request], false
    *         otherwise.
    */
   public final boolean isPQueryRelated() {
      boolean response = false;
      for (int i = 0; i < Protocol.PQ_PROTOCOL_IDENTIFIERS.length; i++) {
         if (Protocol.PQ_PROTOCOL_IDENTIFIERS[i].equals(my_id)) {
            response = true;
            break;
         }
      }
      return response;
   }

   /**
    * Gets the query ID associated with this message if isQueryRelated() == true.
    * 
    * @return the queryID associated with this message, or null if the message does not have a
    *         queryID.
    */
   public final String getQueryID() {
      String result = null;
      if (isPQueryRelated()) {
         result = my_payload.substring(0, QUERY_ID_LENGTH);
      }
      return result;
   }

   /**
    * Gets the payload associated with this message if isQueryRelated() == true.
    * 
    * @return the payload associated with this message, or null if the message does not have a
    *         queryID.
    */
   public final String getQueryPayload() {
      String result = null;
      if (isPQueryRelated()) {
         result = my_payload.substring(QUERY_ID_LENGTH, my_payload.length());
      }
      return result;
   }

   /**
    * Returns the identifier of the message.
    * 
    * @return one of the message constants defined in org.construct_infrastructure.util.Protocol
    */
   public final String getMessageId() {
      return my_id;
   }

   /**
    * Returns the payload of the message.
    * 
    * @return the message payload.
    */
   public final String getPayload() {
      return my_payload;
   }
}
