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
import java.io.InputStream;
import java.io.PrintStream;
import java.net.Socket;
import java.util.logging.Logger;

/**
 * Thread that deals with all client requests.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public abstract class AbstractHandlerThread implements Runnable {

   /**
    * The socket with which communicate with the client.
    */
   private final transient Socket my_clientSocket;

   /**
    * The socket input stream.
    */
   private InputStream my_in;

   /**
    * The socket output stream.
    */
   private PrintStream my_out;

   /**
    * The data port associated with this socket.
    */
   private final transient Logger my_logger;

   /**
    * Creates a new request handler for a given client.
    * 
    * @param a_client
    *           the socket with which communicate with the client.
    * @param a_logger
    *           the logger used to report errors.
    */
   public AbstractHandlerThread(final Socket a_client, final Logger a_logger) {
      super();
      my_logger = a_logger;
      my_clientSocket = a_client;
      try {
         // Connect streams to the sockets
         my_in = my_clientSocket.getInputStream();
         my_out = new PrintStream(my_clientSocket.getOutputStream(), true);
      } catch (IOException e) {
         my_logger.info("Client disconnected");
      }
   }

   /**
    * Takes client data and passes it to the datastore. Response is sent back to the client.
    */
   public abstract void run();

   /**
    * Return the input stream associated with this handler.
    * 
    * @return the input stream associated with this handler.
    */
   public final InputStream getInputStream() {
      return my_in;
   }

   /**
    * Return the logger associated with this handler.
    * 
    * @return the logger associated with this handler.
    */
   public final Logger getLogger() {
      return my_logger;
   }

   /**
    * Return the output stream associated with this handler.
    * 
    * @return the output stream associated with this handler.
    */
   public final PrintStream getOutputStream() {
      return my_out;
   }
   
   /**
    * Return the Socket associated with this handler.
    * 
    * @return the Socket associated with this handler.
    */
   public final Socket getConnection() {
      return my_clientSocket;
   }
}
