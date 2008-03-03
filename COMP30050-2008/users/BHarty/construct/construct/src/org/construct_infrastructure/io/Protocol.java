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
 * This class contains utility methods for dealing with the construct protocols.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class Protocol {

   /**
    * The number of bytes in a message code identifier.
    */
   public static final int MESSAGE_ID_LENGTH = 3;

   /**
    * The number of bytes in the payload length descriptor.
    */
   public static final int PAYLOAD_DESCRIPTOR_SIZE = 10;

   /**
    * The protocol identifier for persistent querying.
    */
   public static final String PERSISTENT_QUERY = "400";
   
   /**
    * The protocol identifier used for responding to persistent queries.
    */
   public static final String PERSISTENT_QUERY_RESPONSE = "410";

   /**
    * The protocol identifier for querying.
    */
   public static final String QUERY = "200";

   /**
    * The protocol identifier used for responding to queries.
    */
   public static final String QUERY_RESPONSE = "210";

   /**
    * The protocol identifier used for sending rdf statements to the data port.
    */
   public static final String RDF_ADD = "100";

   /**
    * The protocol identifier used for responding to an add rdf statements request.
    */
   public static final String RDF_ADD_RESPONSE = "110";

   /**
    * The protocol identifier used for sending a service descriptor.
    */
   public static final String SERVICE_DESCRIPTOR = "310";

   /**
    * The protocol identifier for unsubscribing from a persistent querying.
    */
   public static final String UNSUB_PERSISTENT_QUERY = "450";
   
   /**
    * The identifier representing an OK status message.
    */
   public static final String STATUS_OK = "600";
   
   /**
    * The identifier representing an ERROR status message.
    */
   public static final String STATUS_ERROR = "610";
   
   /**
    * The identifier representing an UNKNOWN status message.
    */
   public static final String STATUS_UNKNOWN = "650";

   /**
    * An array containing all the protocol identifiers. If you add a new protocol then it must
    * be in this list. This array is used to check incoming format requests to make sure the
    * given code is valid. When we move to 1.5 we can use enumerations.
    */
   public static final String[] PQ_PROTOCOL_IDENTIFIERS = {PERSISTENT_QUERY,
                                                           PERSISTENT_QUERY_RESPONSE, 
                                                           UNSUB_PERSISTENT_QUERY };

   /**
    * An array containing all the protocol identifiers bar those dealing with persistent
    * queries. If you add a new protocol then it must be in this list. This array is used to
    * check incoming format requests to make sure the given code is valid. When we move to 1.5
    * we can use enumerations.
    */
   public static final String[] PROTOCOL_IDENTIFIERS = {QUERY, QUERY_RESPONSE, RDF_ADD,
                                                        RDF_ADD_RESPONSE, 
                                                        SERVICE_DESCRIPTOR };
   
   /**
    * A private constructor that exists to defeat instantiation.
    */
   private Protocol() {
      // Exists to defeat instantiation.
   }
   
   /**
    * Encodes a String in preperation for transmition using a given protocol. This method takes
    * the data and code, checks that the code is valid and then returns a new String of the
    * form "&lt;CODE&gt; DATA_PAYLOAD_SIZE_IN_BYTES DATA".
    * 
    * @param some_data
    *           The data to encoded.
    * @param a_code
    *           The code representing the protocol ID.
    * @return The encoded String or null if the code is invalid or format fails.
    */
   public static String format(final String some_data, final String a_code) {
      String response = null;
      for (int i = 0; i < PROTOCOL_IDENTIFIERS.length; i++) {
         if (PROTOCOL_IDENTIFIERS[i].equals(a_code)) {
            response = (a_code + paddedLength(some_data) + some_data);
            break;
         }
      }
      return response;
   }

   /**
    * Encodes a query ID and query or query response in preperation for transmition using a
    * given protocol. This method takes the data and code, checks that the code is valid and
    * then returns a new String of the form "&lt;CODE&gt; DATA_PAYLOAD_SIZE_IN_BYTES DATA".
    * 
    * @param a_queryID
    *           the queryID associated with the request or response.
    * @param some_data
    *           The data to encoded.
    * @param a_code
    *           The code representing the protocol ID.
    * @return The encoded String or null if the code is invalid or format fails.
    */
   public static String format(final String a_queryID, final String some_data,
         final String a_code) {
      String response = null;
      for (int i = 0; i < PQ_PROTOCOL_IDENTIFIERS.length; i++) {
         if (PQ_PROTOCOL_IDENTIFIERS[i].equals(a_code)) {
            response = (a_code + paddedLength(a_queryID + some_data) + a_queryID + some_data);
            break;
         }
      }
      return response;
   }

   /**
    * Creates the 10 bytes containing the length of the payload.
    * 
    * @param some_data
    *           the data to be sent
    * @return a 10 byte string containing the length of the payload
    * @throws IllegalArgumentException
    *            if some_data is null or excedes the maximum length 9.99Gb
    */
   private static String paddedLength(final String some_data) throws IllegalArgumentException {
      final String result = "0000000000";
      String len = "";
      if (some_data == null) {
         throw new IllegalArgumentException("null value for the data string");
      } else {
         len = Integer.valueOf(some_data.length()).toString();
      }

      if (len.length() > PAYLOAD_DESCRIPTOR_SIZE) {
         throw new IllegalArgumentException("data exceeds maximum size (9.99Gby)");
      }

      return result.substring(0, result.length() - len.length()) + len;
   }
}
