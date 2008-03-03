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
package org.construct_infrastructure.component.persistentqueryservice;


import java.io.IOException;
import java.net.Socket;
import java.util.concurrent.TimeoutException;
import java.util.logging.Logger;

import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.io.AbstractHandlerThread;
import org.construct_infrastructure.io.AbstractServiceSocket;
import org.construct_infrastructure.io.Message;
import org.construct_infrastructure.io.MessageReader;
import org.construct_infrastructure.io.Protocol;

/**
 * This is a socket for the persistent query service which receives queries and query
 * cancellations and calls the appropriate method in the persistent query service.
 * 
 * @author Adrian Clear (adrian.clear@ucd.ie)
 */
public class PersistentQueryServiceSocket extends AbstractServiceSocket {

   /**
    * Creates a socket that allows the persistent query service to speak to the outside world.
    * 
    * @param a_logger
    *           The logger associated with this socket.
    * @param a_port
    *           The port that this socket should use. A port of 0 creates a socket on any free
    *           port.
    * @throws IOException
    *            if the socket could not be opened on the requsted port
    */
   public PersistentQueryServiceSocket(final Logger a_logger, final int a_port)
         throws IOException {
      super(a_logger, a_port);
   }

   /**
    * Starts the handler for a new request.
    * 
    * @param a_client
    *           the client connection to the service.
    * @throws IOException
    *            if an error occurs starting the handler
    */
   protected final void startHandler(final Socket a_client) throws IOException {
      getHandlerExecutor().execute(new HandlerThread(a_client, getLogger()));
   }

   /**
    * An instance of the DataPortHandlerThread is spawned to deal with each new incloming
    * request.
    * 
    * @author Adrian Clear (adrian.clear@ucd.ie)
    */
   final class HandlerThread extends AbstractHandlerThread {

      /**
       * The interface for the query service.
       */
      public static final String P_QUERY_SERVICE = "org.construct_infrastructure.component.persistentqueryservice.PersistentQueryService";

      /**
       * Creates a new request handler for a given client.
       * 
       * @param a_client
       *           the socket with which communicate with the client.
       * @param a_logger
       *           the logger used to report error messages
       */
      public HandlerThread(final Socket a_client, final Logger a_logger) {
         super(a_client, a_logger);
      }

      /**
       * Takes client data and passes it to the datastore. Response is sent back to the client.
       */
      public void run() {
         try {
            final PersistentQueryService pQueryService = (PersistentQueryService) ComponentRegistry
                  .getComponent(P_QUERY_SERVICE);
            final MessageReader messageReader = new MessageReader(getInputStream(), getHandlerExecutor());
            while (true) {
               final Message message = messageReader.getMessage();
               if (message != null && pQueryService != null && message.isPQueryRelated()) {
                  if (message.getMessageId().equals(Protocol.PERSISTENT_QUERY)) {
                     final String queryID = message.getQueryID();
                     final String query = message.getQueryPayload();
                     pQueryService.query(query, queryID, getOutputStream());
                  } else if (message.getMessageId().equals(Protocol.UNSUB_PERSISTENT_QUERY)) {
                     final String queryID = message.getQueryID();
                     pQueryService.cancelQuery(queryID);
                  } else {
                     getOutputStream().print(
                           Protocol.format(Protocol.STATUS_UNKNOWN,
                                 Protocol.PERSISTENT_QUERY_RESPONSE));
                  }
               } else {
                  getOutputStream().print(
                        Protocol.format(Protocol.STATUS_UNKNOWN, Protocol.QUERY_RESPONSE));
               }
               getOutputStream().flush();
            }
         } catch (NoSuchComponentException e) {
            getLogger().severe("Could not locate the data port in the component registry");
         } catch (InterruptedException e) {
            getLogger()
                  .warning(
                        "InterruptedException occured while " + "reading message: "
                              + e.getMessage());
         }  catch (TimeoutException e) {
            getLogger().warning(
                  "TimeoutException while reading message: " + e.getMessage());
         }finally {
            try {
               if (getConnection() != null) {
                  getConnection().close();
               }
            } catch (IOException e) {
               getLogger().info("IOException occured while closing socket: " + e.getMessage());
            }
         }
      }
   }
}
