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
package org.construct_infrastructure.component.discovery;


import java.io.IOException;
import java.util.Iterator;
import java.util.Properties;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.io.ServiceComponentDescriptor;

import com.apple.dnssd.DNSSD;
import com.apple.dnssd.DNSSDException;
import com.apple.dnssd.DNSSDRegistration;
import com.apple.dnssd.DNSSDService;
import com.apple.dnssd.RegisterListener;

/**
 * The DiscoveryServiceImpl is the component which clients request descriptions of available
 * Construct services - such as the QueryService. It will tell them what the service is called
 * and how to access it. All communications happen over a raw TCP socket.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 */
public class DiscoveryServiceImpl extends AbstractConstructComponent implements
      DiscoveryService, RegisterListener {

   /**
    * The construct registration string.
    */
   public static final String BONJOUR_REGISTRATION_TYPE = "_construct._tcp";

   /**
    * The fully qualified name of the registry service in the component registry.
    */
   private static final String REGISTRY_SERVICE = "org.construct_infrastructure.component.discovery.RegistryService";

   /**
    * A socket to talk to.
    */
   private DiscoveryServiceSocket my_socket;

   /**
    * A registry of services that have been created and registered with this instance of
    * Construct.
    */
   private RegistryService my_registry;

   /**
    * The ID for this bonjour service name.
    */
   private String my_localNodeID = "CONSTRUCT[" + System.getProperty("user.name")
         + ".discovery]";

   /**
    * Constructor to create the discovery object.
    * 
    * @param some_properties
    *           the props of this discovery service
    */
   public DiscoveryServiceImpl(final Properties some_properties) {
      super();
      setProperties(some_properties);
   }

   /**
    * Sets up links to the registry service component.
    * 
    * @throws NoSuchComponentException
    *            if there is no registry component
    */
   public final void setupComponentLinks() throws NoSuchComponentException {
      my_registry = (RegistryService) ComponentRegistry.getComponent(REGISTRY_SERVICE);
   }

   /**
    * Checks to see if we are running as a server (defined in the properties for this
    * component) and opens up a listener socket if required. This method checks the properties
    * file for the optional port property to decide which port to bind to. If no port is
    * specified the next available port will be used.
    */
   public final void onRun() {
      String portProperty = (String) getProperties().get("port");
         int port = 0; // if we send port 0 to the data port socket it will bind to next
         // available port
         try {
            if (portProperty != null) {
               port = Integer.parseInt(portProperty);
            }
         } catch (NumberFormatException e) {
            getLogger().warning(
                  "Invalid port number specified in properties. Using next available port");
         }
         try {
            my_socket = new DiscoveryServiceSocket(getLogger(), port);
            new Thread(my_socket).start();
            // Register as a bonjour service
            DNSSD.register(0, 0, my_localNodeID, BONJOUR_REGISTRATION_TYPE, "", "", my_socket
                  .getLocalPort(), null, this);
         } catch (IOException e) {
            getLogger().warning(
                  "Could not open discovery service socket to listen for client requests");
         } catch (DNSSDException dnssde) {
            getLogger().severe("Could not register discovery service with bonjour." + dnssde);
         }
   }

   /**
    * Cancel the cycle timer before shutting down.
    */
   public final void onShutdown() {
         my_socket.shutdown();
   }

   /**
    * Returns all the registered service descriptors in XML format.
    * 
    * @return the XML for all service descriptors in the registry
    */
   public final String getServiceDescriptorsAsXML() {
      final StringBuffer buff = new StringBuffer("<services>\n");
      for (final Iterator it = my_registry.serviceDescriptorIterator(); it.hasNext();) {
         final ServiceComponentDescriptor descriptor = (ServiceComponentDescriptor) it.next();
         buff.append(descriptor.marshall()+ "\n");
      }
      buff.append("</services>");
      return buff.toString();
   }

   /**
    * This method is invoked by callback once registered as a bonjour service. When this occurs
    * we need to check if our localID has been changed due to collisions and then browse for
    * other construct deployments.
    * 
    * @see com.apple.dnssd.RegisterListener#serviceRegistered(
    *      com.apple.dnssd.DNSSDRegistration, int, java.lang.String, java.lang.String,
    *      java.lang.String)
    * @param a_registration
    *           The active registration.
    * @param the_flags
    *           Unused.
    * @param a_serviceName
    *           The service name registered.
    * @param the_regType
    *           The type of service registered.
    * @param the_domain
    *           The domain it was registered on.
    */
   public final void serviceRegistered(final DNSSDRegistration a_registration,
         final int the_flags, final String a_serviceName, final String the_regType,
         final String the_domain) {
      // Our name may have been renamed on collision
      my_localNodeID = a_serviceName;
   }

   /**
    * Called if an error occurs during service registration or the browse request.
    * 
    * @param a_service
    *           the service invoking the callback.
    * @param an_errorCode
    *           the code representing the error that occured.
    */
   public final void operationFailed(final DNSSDService a_service, final int an_errorCode) {
      getLogger().severe(
            "Service reported error during registration of discovery service: Error #"
                  + String.valueOf(an_errorCode));
   }

}
