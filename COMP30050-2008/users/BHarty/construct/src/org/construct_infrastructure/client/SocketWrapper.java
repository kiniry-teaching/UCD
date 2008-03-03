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
import java.io.InputStream;
import java.io.PrintStream;
import java.net.Socket;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * This class acts as a wrapper round a socket, handling the protocols to talk to the data port
 * and query service.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public abstract class SocketWrapper {

   /**
    * The local socket.
    */
   final Socket my_socket;

   /**
    * The logger for this class.
    */
   private final Logger my_logger;

   /**
    * The writer for the socket.
    */
   private final PrintStream my_printStream;

   /**
    * The input stream for the socket.
    */
   private final InputStream my_in;

   /**
    * Creates a wrapper round a socket.
    * 
    * @param a_socket
    *           the socket to be wrapped
    * @throws IOException
    *            if an error occurs connecting the writer or reader to the socket.
    */
   public SocketWrapper(final Socket a_socket) throws IOException {
      my_socket = a_socket;
      my_logger = Logger.getLogger(getClass().getName());
      my_logger.setLevel(Level.WARNING);
      my_printStream = new PrintStream(my_socket.getOutputStream(), true);
      my_in = my_socket.getInputStream();
   }

   /**
    * Is the socket closed?
    * 
    * @return true if the socket is closed, false otherwise.
    */
   public final boolean isClosed() {
      boolean response = true;
      if (my_socket != null) {
         response = my_socket.isClosed();
      }
      return response;
   }

   /**
    * Is this socket connected?
    * 
    * @return true if the socket is connected, false otherwise.
    */
   public final boolean isConnected() {
      return !isClosed();
   }

   /**
    * Gets the input stream.
    * 
    * @return the input stream.
    */
   public final InputStream getInputStream() {
      return my_in;
   }

   /**
    * Gets the output stream.
    * 
    * @return the output stream.
    */
   public final PrintStream getPrintStream() {
      return my_printStream;
   }

   /**
    * Closes the socket.
    * 
    * @throws IOException
    *            if an exception occurs closing the socket.
    */
   public abstract void close() throws IOException;

   /**
    * Gives access to the logger for the component.
    * 
    * @return The logger for this component.
    */
   public final Logger getLogger() {
      return my_logger;
   }

}
