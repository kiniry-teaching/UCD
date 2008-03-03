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
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import org.construct_infrastructure.io.MessageReader;

/**
 * This class acts as a wrapper round a socket, handling the protocols to talk to asynchronous
 * services (e.g., the persistent query service).
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class AsyncServiceWrapper extends SocketWrapper implements Runnable {

   /**
    * A constant representing the integer 500.
    */
   private static final int FIVE_HUNDRED = 500;

   /**
    * The handler for messages read from the Socket.
    */
   private AsyncMessageHandler my_messagehandler;

   /**
    * Executor that handles listening for incoming messages.
    */
   private ExecutorService my_executor;

   /**
    * Has an error occured?
    */
   private boolean my_errorOccured;

   /**
    * An executer service used to schefule checks for errors.
    */
   private final ScheduledExecutorService my_service_scheduler;

   /**
    * The message reader associated with this socket.
    */
   private final MessageReader my_messageReader;

   /**
    * Is this service shutting down?
    */
   private boolean my_shouldShutdown;

   /**
    * A runnable object that checks the persistent query service listener for errors.
    */
   private final Runnable my_listenerMonitor = new Runnable() {
      public void run() {
         if (hasErrorOccured() && !isClosed()) {
            try {
               close();
            } catch (IOException e) {
               my_messagehandler.onError(e);
            } finally {
               my_service_scheduler.shutdown();
            }
         }
      }
   };

   /**
    * Creates a wrapper round a socket connection to a synchronous service.
    * 
    * @param a_socket
    *           the socket to be wrapped
    * @param a_messageHandler
    *           the message handler for messages received asynchronously.
    * @throws IOException
    *            if an error occurs connecting the writer or reader to the socket.
    */
   public AsyncServiceWrapper(final Socket a_socket, final AsyncMessageHandler a_messageHandler)
         throws IOException {
      super(a_socket);
      my_errorOccured = false;
      if (a_messageHandler == null) {
         throw new IllegalArgumentException("The message handler must not be null");
      } else {
         my_messagehandler = a_messageHandler;
      }
      my_messageReader = new MessageReader(getInputStream(), my_executor);
      // Use single thread
      my_executor = Executors.newSingleThreadExecutor();
      my_executor.execute(this);
      my_service_scheduler = Executors.newScheduledThreadPool(1);
      my_service_scheduler.scheduleWithFixedDelay(my_listenerMonitor, 0, FIVE_HUNDRED,
            TimeUnit.MILLISECONDS);
      my_shouldShutdown = false;
   }

   /**
    * Writes a formatted string to the socket.
    * 
    * @param a_string
    *           the string to be written to the socket
    * @throws IOException
    *            if an error occurs writing to the socket
    */
   public void writeToSocket(final String a_string) throws IOException {
      // Send data over socket
      getPrintStream().print(a_string);
      getPrintStream().flush();
   }

   /**
    * Listens for messages and passes them to the message handler.
    */
   public void run() {
      while (!my_shouldShutdown || !my_errorOccured) {
         try {
            my_messagehandler.onMessage(my_messageReader.getMessage());
         } catch (InterruptedException e) {
            // Log message if we are not shutting down (message is expected when shutting
            // down).
            if (!my_shouldShutdown) {
               getLogger().warning(
                     "InterruptedException occured while reading message: " + e.getMessage());
               my_messagehandler.onError(e);
            }
            my_errorOccured = true;
         } catch (TimeoutException e) {
            if (!my_shouldShutdown) {
               getLogger()
                     .warning("TimeoutException while reading message: " + e.getMessage());
            }
         }
      }
   }

   /**
    * Closes the socket.
    * 
    * @throws IOException
    *            if an exception occurs closing the socket.
    */
   public void close() throws IOException {
      my_shouldShutdown = true;
      my_messageReader.close();
      my_executor.shutdown();
      my_service_scheduler.shutdown();
      if (my_socket != null && !my_socket.isClosed()) {
         my_socket.close();
      }
      my_executor.shutdown();
   }

   /**
    * Has an error occured in the listener thread?
    * 
    * @return true if an error has occured, false otherwise.
    */
   public boolean hasErrorOccured() {
      return my_errorOccured;
   }

   /**
    * Stop the executor, and close the socket if it is still open.
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
