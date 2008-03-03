//
// $Revision: 7871 $: $Date: 2008-02-25 15:06:55 +0000 (Mon, 25 Feb 2008) $ - $Author: gstevenson $
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
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeoutException;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.construct_infrastructure.io.Message;
import org.construct_infrastructure.io.MessageReader;
import org.construct_infrastructure.io.ServiceComponentDescriptor;

/**
 * Client-side proxy object that can talk to a Construct discovery service, find services and
 * interact with them.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public abstract class AbstractClientProxy {

   /**
    * The port on which the Construct bonjour proxy is running.
    */
   private static final int LOCAL_CONSTRUCT_BONJOUR_PROXY_PORT = 3826;

   /**
    * The length of the &lt;/serviceComponentDescriptor&gt; tag.
    */
   private static final int SERVICE_COMPONENT_DESCRIPTOR_END_TAG_LENGTH = 29;

   /**
    * The logger for this class.
    */
   private final Logger my_logger;

   /**
    * Creates a new instance of the proxy and starts a bonjour listener.
    */
   public AbstractClientProxy() {
      // Set up the logger
      my_logger = Logger.getLogger(getClass().getName());
      getLogger().setLevel(Level.ALL);
   }

   /**
    * Gives access to the logger for the component.
    * 
    * @return The logger for this component.
    */
   public final Logger getLogger() {
      return my_logger;
   }

   /**
    * Calls the listener and attempts to connect to a service.
    * 
    * @param a_serviceName
    *           the name of the service we wish to connect to.
    * @throws ServiceException
    *            if the named serice cannot be found. *
    * @throws IOException
    *            if the local proxy cannot be contacted.
    * @return a SocketWrapper round the desired service
    */
   protected final Socket getService(final String a_serviceName) throws IOException,
         ServiceException {
      Socket socket = null;
      // attempt to connect to the local bonjour proxy to get service descriptors
      // We want to get the service descriptors for an instance of construct
      // Iterate through them until we successfully resolve
      List serviceDescriptors;
      final String xmlServiceDescriptors = getXMLServiceDescriptors();
      if (xmlServiceDescriptors != null) {
         serviceDescriptors = getServiceDescriptors(xmlServiceDescriptors);

         // Sort the service descriptors to prefer the local host.
         Collections.sort(serviceDescriptors);

         // Now check for the named service in the set of descriptors
         socket = searchForAndConnectToService(serviceDescriptors, a_serviceName);
      }
      // At this point we either sucessfully connected to the service, or no service of that
      // name is known. If we were unsuccessful, we throw an exception
      if (socket == null) {
         throw new ServiceException("Found no running instances of a service with name: "
               + a_serviceName);
      }
      return socket;
   }

   /**
    * Iterate through a collection of services looking for a named service. We then try to
    * connect to that service.
    * 
    * @param the_services
    *           the collection of services to look through.
    * @param the_serviceName
    *           the name of the service we want to connect to.
    * @return a connected Socket to the service, or null if we could not obtain a connection.
    */
   private Socket searchForAndConnectToService(final Collection the_services,
         final String the_serviceName) {
      Socket commsSocket = null;
      boolean connected = false;
      final Iterator it = the_services.iterator();
      while (it.hasNext() && !connected) {
         final ServiceComponentDescriptor descriptor = (ServiceComponentDescriptor) it.next();
         if (descriptor.getName().equals(the_serviceName)) {
            try {
               commsSocket = new Socket(descriptor.getHost(), descriptor.getPort());
               connected = true;
            } catch (UnknownHostException uhe) {
               System.err.println("Unknown host: " + descriptor.getHost() + ":"
                     + descriptor.getPort() + uhe);
            } catch (IOException ioe) {
               System.err.println("Socket comms failure: " + descriptor.getHost() + ":"
                     + descriptor.getPort());
            }
            my_logger.info("Connected to "+the_serviceName+" on "+descriptor.getHost()+":"+descriptor.getPort());
         }
      }
      return commsSocket;
   }

   /**
    * Get the service descriptors in a Collection of ServiceComponentDescovery objects.
    * 
    * @param the_xmlDescriptors
    *           the service descriptors in XML format.
    * @return the collection of ServiceComponentDescriptor objects (which could be empty)
    */
   private List getServiceDescriptors(final String the_xmlDescriptors) {
      final List serviceDescriptors = new ArrayList();
      int startPos = the_xmlDescriptors.indexOf("<servicecomponentdescriptor>");
      while (startPos != -1) {
         final int endPos = the_xmlDescriptors.indexOf("</servicecomponentdescriptor>",
               startPos)
               + SERVICE_COMPONENT_DESCRIPTOR_END_TAG_LENGTH;
         final ServiceComponentDescriptor descriptor = ServiceComponentDescriptor
               .unmarshal(the_xmlDescriptors.substring(startPos, endPos));
         serviceDescriptors.add(descriptor);
         startPos = the_xmlDescriptors.indexOf("<servicecomponentdescriptor>", endPos);
      }
      return serviceDescriptors;
   }

   /**
    * Get the service descriptors in a big XML string.
    * 
    * @return the XML form of the service descriptors (which could just be
    *         &lt;services>&lt;/services> or null if we are not connected to an instance of
    *         Construct
    * @throws IOException
    *            if the local proxy cannot be contacted.
    */
   private String getXMLServiceDescriptors() throws IOException {
      Socket toConstruct = null;
      String result = null;
      final ExecutorService executorService = Executors.newSingleThreadExecutor();
      try {
         toConstruct = new Socket("localhost", LOCAL_CONSTRUCT_BONJOUR_PROXY_PORT);
         // Process message from discovery service
         final MessageReader messageReader = new MessageReader(toConstruct.getInputStream(),
                executorService);
         final Message message = messageReader.getMessage();
         result = message.getPayload();
      } catch (IOException ioe) {
         throw new IOException("Could not connect to the local proxy service. "
               + "Are you sure it is running?\nTry running \"telnet localhost 3826\" "
               + "from a command prompt to check.");
      } catch (InterruptedException e) {
         getLogger().warning(
               "InterruptedException " + "occured while " + "reading message: "
                     + e.getMessage());
      } catch (TimeoutException e) {
         getLogger().warning("TimeoutException while reading message: " + e.getMessage());
      } finally {
         if (toConstruct != null) {
            try {
               toConstruct.close();
            } catch (IOException e) {
               System.err.println("Could not close socket: " + e.getMessage());
            }
         }
         if (executorService != null) {
            executorService.shutdown();
         }
      }
      return result;
   }
}
