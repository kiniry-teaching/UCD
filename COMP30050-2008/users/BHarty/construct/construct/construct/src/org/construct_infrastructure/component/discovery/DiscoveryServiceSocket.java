//
// $Revision: 7904 $: $Date: 2008-02-26 16:41:59 +0000 (Tue, 26 Feb 2008) $ - $Author: lorcan $
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
package org.construct_infrastructure.component.discovery;


import java.io.IOException;
import java.net.Socket;
import java.util.logging.Logger;

import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.io.AbstractHandlerThread;
import org.construct_infrastructure.io.AbstractServiceSocket;
import org.construct_infrastructure.io.Protocol;

/**
 * The DiscoveryServiceSocket replies to incoming requests for service descriptors from
 * clients.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
final class DiscoveryServiceSocket extends AbstractServiceSocket {

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
   public DiscoveryServiceSocket(final Logger a_logger, final int a_port) throws IOException {
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
    * An instance of the DataPortHandlerThread is spawned to deal with each new incoming
    * request.
    * 
    * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
    */
   final class HandlerThread extends AbstractHandlerThread {

      /**
       * The interface for the query service.
       */
      public static final String DISCOVERY_SERVICE = "org.construct_infrastructure.component.discovery.DiscoveryService";

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
       * Sends all the service descriptors to the client and closes socket.
       */
      public void run() {
         // Lookup query service from the component registry
         DiscoveryService discoveryService = null;
         try {
            discoveryService = (DiscoveryService) ComponentRegistry
                  .getComponent(DISCOVERY_SERVICE);
         } catch (NoSuchComponentException e) {
            getLogger().severe("Could not locate the data port in the component registry");
         }
         // Get all the service descriptors and send to the client
         getOutputStream().print(
               Protocol.format(discoveryService.getServiceDescriptorsAsXML(),
                     Protocol.SERVICE_DESCRIPTOR));
         getOutputStream().flush();
         try {
            if (getConnection() != null) {
               getConnection().close();
            }
         } catch (IOException e) {
            getLogger()
                  .info(
                        "Client connection reset before discovery service request handler could close it.");
         }
      }
   }

}
