//
// $Revision: 7817 $: $Date: 2008-02-21 11:29:44 +0000 (Thu, 21 Feb 2008) $ - $Author: sneely $
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
package org.construct_infrastructure.component.httpport;


import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.net.Socket;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.io.AbstractHandlerThread;
import org.construct_infrastructure.io.AbstractServiceSocket;

/**
 * The HttpPortSocket allows HTTP aware applications and entities to connect to it in order to
 * get data from Construct.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 */
public class HttpPortSocket extends AbstractServiceSocket {

   /**
    * Creates a socket that allows the http port to speak to the outside world.
    * 
    * @param a_logger
    *           The logger associated with this socket.
    * @param a_port
    *           The port that this socket should use. A port of 0 creates a socket on any free
    *           port.
    * @throws IOException
    *            if the socket could not be opened on the requested port
    */
   public HttpPortSocket(final Logger a_logger, final int a_port) throws IOException {
      super(a_logger, a_port);
   }

   /**
    * Starts the handler for a new request.
    * 
    * @param a_client
    *           The client connection to the service.
    * @throws IOException
    *            if an error occurs starting the handler
    */
   protected final void startHandler(final Socket a_client) throws IOException {
      try {
         getHandlerExecutor().execute(new HandlerThread(a_client, getLogger()));
      } catch (NoSuchComponentException e) {
         getLogger().severe("Could not locate the HttpPort component: " + e.getMessage());
      }
   }

   /**
    * An instance of the HttpPortHandlerThread is spawned to deal with each new incloming
    * request.
    * 
    * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
    * @author Steve Neely (steve.neely@ucd.ie)
    */
   final class HandlerThread extends AbstractHandlerThread {

      /**
       * The interface for the data port.
       */
      public static final String HTTP_PORT = "org.construct_infrastructure.component"
            + ".httpport.HttpPort";

      /**
       * The local httpport.
       */
      private final HttpPort my_httpPort;

      /**
       * Creates a new request handler for a given client.
       * 
       * @param a_client
       *           the socket with which communicate with the client.
       * @param a_logger
       *           the logger used to report error messages
       * @throws NoSuchComponentException
       *            if a reference to the DataPort cannot be found.
       */
      public HandlerThread(final Socket a_client, final Logger a_logger)
            throws NoSuchComponentException {
         super(a_client, a_logger);
         // Lookup data port from the component registry
         my_httpPort = (HttpPort) ComponentRegistry.getComponent(HTTP_PORT);
      }

      /**
       * Takes client data and passes it to the http port. Response is sent back to the client.
       */
      public void run() {
         
      // HTTP 1.1 messages look like this:
      // message-header = field-name ":" [ field-value ]
  	  // http://www.w3.org/Protocols/rfc2616/rfc2616-sec4.html#sec4.2
         
         BufferedReader br = new BufferedReader(new InputStreamReader(getInputStream()));
         try {
			StringBuffer request = new StringBuffer();
			int contentLength = 0;
			 while (br.ready()) {
				 String line = br.readLine();

				 if (line.toLowerCase().startsWith("content-length:")) {
					 Pattern pattern = Pattern.compile("[\\d]+"); // use regexp to find the sequence of digits that tell us how much content to expect
					 Matcher matcher = pattern.matcher(line);
					 if (matcher.find()) {
						contentLength = Integer.parseInt(matcher.group());
					 }
				 }
				 request.append(line + "\r\n"); // get the entire HTTP header and add the CrLf back on that br.readLine() took off
				 if (line.equals("") && contentLength > 0) { // there is a blank line before the message body
					 char[] messageBody = new char[contentLength];
					 br.read(messageBody); // read the message body (POST data)
					 request.append(messageBody);
				 }
			 }   	 
        	 
            handleMessage(request.toString());
          } catch (IOException ioe) {
            getLogger().warning(
                  "IO while reading message: " + ioe.getMessage());
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

      /**
       * Gets payload of message, sends to http port then and responds to the caller.
       * 
       * @param a_request
       *           the message to be processed.
       */
      private void handleMessage(final String a_request) {
         PrintStream ps = new PrintStream(getOutputStream());
         // If message is valid pass it on
         if (a_request != null && my_httpPort != null) {
            // Run the client request
            final String response = my_httpPort.handleRequest(a_request);
            // Send response to the client to indicate success of operation.
//            getOutputStream().print(response);
            try {
               ps.write(response.getBytes());
            } catch (Exception e) {
               e.printStackTrace();
            }
         }
         ps.flush();
      }
   }
}
