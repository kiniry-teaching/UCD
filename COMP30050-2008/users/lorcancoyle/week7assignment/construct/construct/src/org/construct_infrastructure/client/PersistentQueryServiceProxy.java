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
package org.construct_infrastructure.client;


import java.io.IOException;
import java.io.StringReader;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Hashtable;
import java.util.Map;

import org.construct_infrastructure.component.persistentqueryservice.PersistentQueryService;
import org.construct_infrastructure.exception.ConstructRuntimeException;
import org.construct_infrastructure.io.Message;
import org.construct_infrastructure.io.Protocol;

import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.query.ResultSetFactory;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;

/**
 * This class acts as a proxy for contact the query service, abstraction the details of
 * discovery and communications from the developer. TODO: Need to deal with query maintenance
 * when a connection is lost.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class PersistentQueryServiceProxy extends AbstractClientProxy implements
      AsyncMessageHandler {

   /**
    * The number of bits in a nibble.
    */
   private static final int NIBBLE_SIZE = 4;

   /**
    * A map containg asynchronous query information.
    */
   private Map my_asyncQueries;

   /**
    * The active connection to the persistent query service.
    */
   private AsyncServiceWrapper my_persistentQueryServiceSocket;

   /**
    * Creates a new instance of the persistent query service proxy and starts scanning for
    * Construct instances.
    */
   public PersistentQueryServiceProxy() {
      super();
      my_asyncQueries = new Hashtable();

   }

   /**
    * Gets a connection to a PersistentQueryService.
    * 
    * @return a connection to the PersistentQueryService
    * @throws ServiceException
    *            if a connection could not be established.
    * @throws IOException
    *            if an error occurs adding the wrapper to the socket.
    */
   private AsyncServiceWrapper getPersistentQueryServiceConnection() throws ServiceException,
         IOException {
      AsyncServiceWrapper wrapper = null;
      if (my_persistentQueryServiceSocket != null
            && !my_persistentQueryServiceSocket.isClosed()) {
         wrapper = my_persistentQueryServiceSocket;
      } else {
         wrapper = new AsyncServiceWrapper(getService(PersistentQueryService.PQS_NAME), this);
         my_persistentQueryServiceSocket = wrapper;
      }
      return wrapper;
   }

   /**
    * Constructs an ResultSet object from an RDF string.
    * 
    * @param a_resultString
    *           the string containing the RDF representation of the result set
    * @return the ResultSet object created from the input string.
    */
   private ResultSet createResultSet(final String a_resultString) {
      ResultSet resultSet;
      // Create a result set
      final Model model = ModelFactory.createDefaultModel();
      final StringReader modelReader = new StringReader(a_resultString);
      model.read(modelReader, null, "N-TRIPLE");
      resultSet = ResultSetFactory.fromRDF(model);
      return resultSet;
   }

   /**
    * Sends an asynchronous SPARQL query to Construct. Note that each query must be unique.
    * 
    * @param a_query
    *           the query to be submitted.
    * @param an_object
    *           the object to callback.
    * @param a_methodName
    *           the method to call on the object.
    * @throws NoSuchMethodException
    *            if the method indicated does not exist.
    * @throws ServiceException
    *            if a connection could not be established.
    * @throws IOException
    *            if an error occurs while contacting the persistent query service.
    * @throws QueryAlreadyExistsException
    *            if the same query has already been subscribed to from this client.
    */
   public void setupAsyncQuery(final String a_query, final String a_methodName,
         final Object an_object) throws NoSuchMethodException, ServiceException, IOException,
         QueryAlreadyExistsException {
      // If callback details are correct, setup query. If not, throw an exception.
      if (methodExists(an_object, a_methodName)) {
         // Generate a queryID
         try {
            final MessageDigest digest = MessageDigest.getInstance("SHA-1");
            digest.update(a_query.getBytes());
            final String queryID = byteArrayToHexString(digest.digest());
            if (my_asyncQueries.containsKey(queryID)) {
               throw new QueryAlreadyExistsException(a_query);
            } else {
               final AsyncServiceWrapper queryService = getPersistentQueryServiceConnection();
               queryService.writeToSocket(Protocol.format(queryID, a_query,
                     Protocol.PERSISTENT_QUERY));
               // Add details to map
               final Object[] callbackDetails = {an_object, a_methodName};
               my_asyncQueries.put(queryID, callbackDetails);
            }
         } catch (NoSuchAlgorithmException e) {
            throw new ConstructRuntimeException(
                  "The SHA algorithm is not installed - cannot generate query IDs");
         }
      } else {
         throw new NoSuchMethodException("No method named " + a_methodName
               + " with a String argument could be found.");
      }
   }

   /**
    * Stops further execution of asynchronous query.
    * 
    * @param a_query
    *           the query to be removed.
    * @throws ServiceException
    *            if a connection could not be established.
    * @throws IOException
    *            if an error occurs while contacting the data port
    */
   public void removeAsynchronousQuery(final String a_query) throws ServiceException,
         IOException {
      // Generate the queryID
      try {
         final MessageDigest digest = MessageDigest.getInstance("SHA-1");
         digest.update(a_query.getBytes());
         final String queryID = byteArrayToHexString(digest.digest());
         // Check that is the query is in the map.
         if (my_asyncQueries.containsKey(queryID)) {
            // Remove from map
            my_asyncQueries.remove(queryID);
            final AsyncServiceWrapper queryService = getPersistentQueryServiceConnection();
            queryService.writeToSocket(Protocol.format(a_query,
                  Protocol.UNSUB_PERSISTENT_QUERY));
         }
      } catch (NoSuchAlgorithmException e) {
         throw new ConstructRuntimeException(
               "The SHA algorithm is not installed - cannot generate query IDs");
      }
   }

   /**
    * This method is responsible for looking up the method associated with a queryID and
    * passing the results of a query to it.
    * 
    * @param a_query_id
    *           the query id associated with the response.
    * @param a_resultSet
    *           the result set associated with the evaluated query.
    */
   public void handleQueryResponse(final String a_query_id, final ResultSet a_resultSet) {
      // Lookup callback details
      final Object[] callbackDetails = (Object[]) my_asyncQueries.get(a_query_id);
      if (callbackDetails != null) {
         final Object object = (Object) callbackDetails[0];
         final String methodName = (String) callbackDetails[1];
         final Class a_class = object.getClass();
         final Class[] arguments = {ResultSet.class};
         final Object[] response = {a_resultSet};
         try {
            final Method declaredMethod = a_class.getDeclaredMethod(methodName, arguments);
            declaredMethod.setAccessible(true);
            declaredMethod.invoke(object, response);
         } catch (NoSuchMethodException e) {
            // Sould never be called
            throw new ConstructRuntimeException("Method not found when attempting callback: "
                  + methodName, e);
         } catch (SecurityException e) {
            throw new ConstructRuntimeException(
                  "A Security Manager prevented access to the application through reflection",
                  e);
         } catch (IllegalAccessException e) {
            throw new ConstructRuntimeException(
                  "An IllegalAccessException occured when attempting a callback: "
                        + methodName, e);
         } catch (InvocationTargetException e) {
            throw new ConstructRuntimeException(
                  "An InvocationTargetException occured when attempting a callback: "
                        + methodName, e);
         }
      }
   }

   /**
    * This method handles asynchronous messages received from the persistent query service.
    * 
    * @param a_message
    *           the message received
    */
   public void onMessage(final Message a_message) {
      ResultSet resultSet = null;
      // Check the message is a query response
      if (a_message.getMessageId().equals(Protocol.PERSISTENT_QUERY_RESPONSE)) {
         if (!a_message.getQueryPayload().startsWith("ERROR:")) {
            resultSet = createResultSet(a_message.getQueryPayload());
         }
         handleQueryResponse(a_message.getQueryID(), resultSet);
      } else {
         getLogger().info(
               "Message received not related to a persistent query: " + a_message.getQueryID()
                     + " - " + a_message.getPayload());
      }
   }

   /**
    * This method handles error messages raised during processing of asynchronous messages.
    * Currently, this only involves logging.
    * 
    * @param an_exception
    *           the error raised when handing an asynchronous message.
    */
   public void onError(final Exception an_exception) {
      // Log the error message
      getLogger().info("Error processing asynchronous message: " + an_exception.getMessage());
   }

   /**
    * This method checks that a given object contains the named method, taking a single string
    * as an argument.
    * 
    * @param a_methodName
    *           the name of the method we want to check for
    * @param an_object
    *           the object to callback.
    * @return true if the method exists, false otherwise.
    */
   private boolean methodExists(final Object an_object, final String a_methodName) {
      boolean response = true;
      final Class a_class = an_object.getClass();
      final Class[] arguments = {ResultSet.class};
      try {
         a_class.getDeclaredMethod(a_methodName, arguments);
      } catch (NoSuchMethodException e) {
         response = false;
      } catch (SecurityException e) {
         throw new ConstructRuntimeException(
               "A Security Manager prevented access to the application through reflection");
      }
      return response;
   }

   /**
    * Is the connection to the persistent query service active?
    * 
    * @return true if the connection is up and no error has occured, false otherwise.
    */
   public boolean isPersistentQueryServiceActive() {
      boolean response = false;
      if (my_persistentQueryServiceSocket != null) {
         response = my_persistentQueryServiceSocket.isConnected();
      }
      return response;
   }

   /**
    * Convert a byte[] array to readable string format. This makes the hex readable. From -
    * http://www.devx.com/tips/Tip/13540
    * 
    * @return result String buffer in String format
    * @param a_string
    *           byte[] buffer to convert to string format
    */
   static String byteArrayToHexString(final byte[] a_string) {
      byte ch = 0x00;
      int i = 0;
      if (a_string == null || a_string.length <= 0)
         return null;
      final String[] pseudo = {"0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B",
                               "C", "D", "E", "F"};
      final StringBuffer out = new StringBuffer(a_string.length * 2);
      while (i < a_string.length) {
         ch = (byte) (a_string[i] & 0xF0);
         // Strip off high nibble
         ch = (byte) (ch >>> NIBBLE_SIZE);
         // shift the bits down
         ch = (byte) (ch & 0x0F);
         // must do this is high order bit is on!
         out.append(pseudo[(int) ch]);
         // convert the nibble to a String Character
         ch = (byte) (a_string[i] & 0x0F);
         // Strip off low nibble
         out.append(pseudo[(int) ch]);
         // convert the nibble to a String Character
         i++;
      }
      final String rslt = new String(out);
      return rslt;
   }

   /**
    * Stops listening for messages.
    * 
    * @throws IOException
    *            if an error occurs shutting down the socket.
    */
   public void close() throws IOException {
      if (my_persistentQueryServiceSocket != null) {
         my_persistentQueryServiceSocket.close();
      }
   }
}
