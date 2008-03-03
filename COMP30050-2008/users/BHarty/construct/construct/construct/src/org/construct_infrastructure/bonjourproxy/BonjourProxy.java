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

package org.construct_infrastructure.bonjourproxy;

import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

import com.apple.dnssd.DNSSDException;

/**
 * Client-side proxy object that can talk to a Construct discovery service, find services and
 * interact with them.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public class BonjourProxy extends Thread {

   /**
    * The port to run the service on.
    */
   private static final int MY_PORT = 3826;

   /**
    * The bonjour listener associated with the proxy.
    */
   private final ProxyBonjourListener my_listener;

   /**
    * The logger for this class.
    */
   private final Logger my_logger;

   /**
    * A socket to talk to.
    */
   private ProxySocket my_socket;

   /**
    * Creates a new instance of the proxy and starts a bonjour listener.
    * 
    * @throws DNSSDException
    *            if the bonjour browse operation fails.
    */
   public BonjourProxy() throws DNSSDException {
      super();
      // Set up the logger
      my_logger = Logger.getLogger(getClass().getName());
      my_logger.setLevel(Level.ALL);

      // Set up the listener
      my_listener = new ProxyBonjourListener(my_logger);

      // open the port
      try {
         my_socket = new ProxySocket(this, MY_PORT, my_logger);
         new Thread(my_socket).start();
         // Register as a bonjour service
      } catch (IOException e) {
         my_logger.warning("Could not open proxy"
               + " socket to start proxy service.");
      }
   }

   /**
    * Calls the listener and attempts to connect to a service.
    * 
    * @return a dsescriptor document for available services
    */
   protected final String getServiceDescriptors() {
      String response = null;
      try {
         response = my_listener.getServiceDescriptors();
      } catch (InterruptedException e) {
         my_logger.warning("Error occured while getting service descriptors: "
               + e.getMessage());
      } catch (ServiceException e) {
         // No instance of construct available
         my_logger.warning("No instance of construct available");
      }

      return response;
   }

   /**
    * Method that shuts down the proxy and kills the running process. Calls System.exit(0) so
    * do this at the very end of your code.
    */
   public final void shutdown() {
      my_socket.shutdown();
   }

//   /**
//    * Main method - used for launching the proxy without the service wrapper.
//    * 
//    * @param some_args
//    *           not used
//    * @throws DNSSDException
//    *            if an error occurs while setting up the Bonjour listener
//    */
//   public static final void main(final String[] some_args) throws DNSSDException {
//      final BonjourProxy proxy = new BonjourProxy();
//   }
}
