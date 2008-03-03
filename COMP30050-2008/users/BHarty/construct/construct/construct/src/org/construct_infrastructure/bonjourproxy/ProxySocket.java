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
package org.construct_infrastructure.bonjourproxy;


import java.io.IOException;
import java.net.Socket;
import java.util.logging.Logger;

import org.construct_infrastructure.io.AbstractHandlerThread;
import org.construct_infrastructure.io.AbstractServiceSocket;
import org.construct_infrastructure.io.Protocol;

/**
 * The DiscoveryServiceSocket replies to incoming requests for service descriptors from
 * clients.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
final class ProxySocket extends AbstractServiceSocket {

   /**
    * The proxy associated with this socket.
    */
   private final BonjourProxy my_bonjourProxy;

   /**
    * Creates a socket that allows the bonjour proxy to speak to the outside world.
    * 
    * @param a_logger
    *           The logger associated with this socket.
    * @param a_port
    *           The port that this socket should use. A port of 0 creates a socket on any free
    *           port.
    * @param a_proxy
    *           the BonjourProxy that this socket belongs to.
    * @throws IOException
    *            if the socket could not be opened on the requsted port
    */
   public ProxySocket(final BonjourProxy a_proxy, final int a_port, final Logger a_logger)
      throws IOException {
      super(a_logger, a_port);
      my_bonjourProxy = a_proxy;
   }

   /**
    * Starts the handler for a new request.
    * 
    * @param a_client
    *           The client connection to the proxy.
    * @throws IOException
    *            if an error occurs starting the handler
    */
   protected void startHandler(final Socket a_client) throws IOException {
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
      public static final String DISCOVERY_SERVICE = "org.construct_infrastructure.component "
            + ".discovery.DiscoveryService";

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
         // Get all the service descriptors and send to the client
         getOutputStream().print(
               Protocol.format(my_bonjourProxy.getServiceDescriptors(),
                     Protocol.SERVICE_DESCRIPTOR));
         getOutputStream().flush();
         try {
            if (getConnection() != null) {

               getConnection().close();
            }
         } catch (IOException e) {
            getLogger().info(
                  "Client connection reset before discovery service"
                        + " request handler could close it.");
         }
      }
   }

}
