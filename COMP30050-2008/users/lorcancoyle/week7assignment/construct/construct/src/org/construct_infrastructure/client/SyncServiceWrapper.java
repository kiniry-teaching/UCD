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
import java.net.Socket;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeoutException;

import org.construct_infrastructure.io.Message;
import org.construct_infrastructure.io.MessageReader;

/**
 * This class acts as a wrapper round a socket, handling the protocols to talk to synchronous
 * services (e.g., the data port and query service).
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class SyncServiceWrapper extends SocketWrapper {

   /**
    * The message reader associated with this socket.
    */
   final MessageReader my_messageReader;

   /**
    * Executor that handles listening for incoming messages.
    */
   private ExecutorService my_executor;
   
   /**
    * Creates a wrapper round a socket connection to a synchronous service.
    * 
    * @param a_socket
    *           the socket to be wrapped
    * @throws IOException
    *            if an error occurs connecting the writer or reader to the socket.
    */
   public SyncServiceWrapper(final Socket a_socket) throws IOException {
      super(a_socket);
      my_executor = Executors.newSingleThreadExecutor();
      my_messageReader = new MessageReader(getInputStream(), my_executor);
   }

   /**
    * Writes a formatted string to the socket and returns the response as a Message object.
    * 
    * @param a_string
    *           the string to be written to the socket
    * @throws IOException
    *            if an error occurs writing to the socket
    * @return the response message from the connected service.
    */
   public Message writeToSocket(final String a_string) throws IOException, TimeoutException {
      // Send data over socket
      getPrintStream().print(a_string);
      getPrintStream().flush();
      // Receive text from server
      // Get message from the message reader
      Message message = null;
      try {
         message = my_messageReader.getMessage();
      } catch (InterruptedException e) {
         getLogger().warning(
               "InterruptedException occured while " + "reading message: " + e.getMessage());
      }
      return message;

   }

   /**
    * Closes the socket.
    * 
    * @throws IOException
    *            if an exception occurs closing the socket.
    */
   public void close() throws IOException {
      my_messageReader.close();
      if (my_socket != null && !my_socket.isClosed()) {
         my_socket.close();
      }
      my_executor.shutdown();
   }

   /**
    * Whether the message reader associated with this wrapper has timed out.
    * 
    * @return true if it has timed out, false otherwise.
    */
   public boolean hasTimedOut(){
      return my_messageReader.hasTimedOut();
   }
   /**
    * Close the socket if it is still open.
    * 
    * @throws Throwable -
    *            all thrown exceptions ignored.
    */
   protected void finalize() throws Throwable {
      try {
         close();
      } catch (IOException e) {
         super.finalize();
      }
   }
}
