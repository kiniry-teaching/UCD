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

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.logging.Logger;

/**
 * The DataPortSocket allows applications and entities to connect to it in order to submit data
 * to construct.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public abstract class AbstractServiceSocket implements ServiceSocket {

   /**
    * The logger associated with this socket.
    */
   private final transient Logger my_logger;

   /**
    * Whether the socket server should shutdown.
    */
   private boolean my_shouldShutdown;

   /**
    * The socket associated with this class.
    */
   private final transient ServerSocket my_socket;

   /**
    * The executor that services incoming requests.
    */
   private final transient ExecutorService my_handlerExecutor;

   /**
    * Creates a socket that allows the data port to speak to the outside world.
    * 
    * @param a_logger
    *           The logger associated with this socket.
    * @param a_port
    *           The port that this socket should use. A port of 0 creates a socket on any free
    *           port.
    * @throws IOException
    *            if the socket could not be opened on the requsted port
    */
   public AbstractServiceSocket(final Logger a_logger, final int a_port) throws IOException {
      super();
      my_logger = a_logger;
      my_socket = new ServerSocket(a_port);
      my_shouldShutdown = false;
      // Creates an Executor that uses a thread pool
      // operating off an unbounded queue.
      // This can be modified if performance becomes an issue
      my_handlerExecutor = Executors.newCachedThreadPool();
   }

   /**
    * Listens to the socket for incoming requests.
    */
   public final void run() {
      while (!my_shouldShutdown) {
         try {
            startHandler(my_socket.accept());
         } catch (IOException e) {
            if (!my_shouldShutdown) {
               my_logger.warning("IO error while waiting for connections: " + e.getMessage());
            }
         }
      }
   }

   /**
    * Starts the handler for a new request.
    * 
    * @param a_client
    *           The client connection to the service.
    * @throws IOException
    *            if an error occurs starting the handler
    */
   protected abstract void startHandler(Socket a_client) throws IOException;

   /**
    * is the socket closed?
    * 
    * @return true if the socket is closed, false otehrwise.
    */
   public final boolean isClosed() {
      return my_socket.isClosed();
   }

   /**
    * Closes the socket when the object is shutdown.
    */
   public final void shutdown() {
      my_shouldShutdown = true;
      try {
         if (my_socket != null) {
            my_socket.close();
         }
         my_handlerExecutor.shutdown();
      } catch (IOException e) {
         my_logger.warning("Could not close socket");
      }
   }

   /**
    * Returns the port on which this socket is listening.
    * 
    * @return the port number to which this socket is listening or -1 if the socket is not yet
    *         bound
    */
   public final int getLocalPort() {
      return my_socket.getLocalPort();
   }

   /**
    * Return the logger associated with this service.
    * 
    * @return the logger associated with this service.
    */
   public final Logger getLogger() {
      return my_logger;
   }

   /**
    * Returns the socket handler executor associated with this service.
    * 
    * @return the socket handler executor associated with this service.
    */
   public final ExecutorService getHandlerExecutor() {
      return my_handlerExecutor;
   }
}
