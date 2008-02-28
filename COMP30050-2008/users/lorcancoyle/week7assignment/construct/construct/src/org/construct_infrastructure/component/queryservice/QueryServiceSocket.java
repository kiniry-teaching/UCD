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
package org.construct_infrastructure.component.queryservice;


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
 * The QueryServiceSocket allows applications and entities to connect to it in order to submit
 * queries to the QueryService.
 * 
 * @author Adrian Clear (adrian.clear@ucd.ie)
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
final class QueryServiceSocket extends AbstractServiceSocket {

   /**
    * Creates a socket that allows the query service to speak to the outside world.
    * 
    * @param a_logger
    *           The logger associated with this socket.
    * @param a_port
    *           The port that this socket should use. A port of 0 creates a socket on any free
    *           port.
    * @throws IOException
    *            if the socket could not be opened on the requsted port
    */
   public QueryServiceSocket(final Logger a_logger, final int a_port) throws IOException {
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
    * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
    */
   final class HandlerThread extends AbstractHandlerThread {

      /**
       * The interface for the query service.
       */
      public static final String QUERY_SERVICE = "org.construct_infrastructure.component.queryservice.QueryService";

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
            // Lookup query service from the component registry
            QueryService queryService = null;
            queryService = (QueryService) ComponentRegistry.getComponent(QUERY_SERVICE);
            MessageReader messageReader = new MessageReader(getInputStream(), getHandlerExecutor());
            while (true) {
               // Get message from the input stream
               Message message = messageReader.getMessage();
               // If message is valid and we recognise the protocol
               if (message != null && queryService != null) {
                  if (message.getMessageId().equals(Protocol.QUERY)) {
                     // Run the client request
                     final String response = queryService.synchronousQuery(message
                           .getPayload());
                     // Send response back to the client to let them know if the input was
                     // successful.
                     if (response != null) {
                        getOutputStream().print(
                              Protocol.format(response, Protocol.QUERY_RESPONSE));
                     } else {
                        getOutputStream().print(
                              Protocol.format(Protocol.STATUS_ERROR, Protocol.QUERY_RESPONSE));
                     }
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
         } catch (TimeoutException e) {
            getLogger().fine("TimeoutException while reading message: " + e.getMessage());
         } finally {
            // Close the socket
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
