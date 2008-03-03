//
// $Revision: 7918 $: $Date: 2008-02-27 11:18:32 +0000 (Wed, 27 Feb 2008) $ - $Author: lorcan $
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
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.locks.ReentrantLock;
import java.util.logging.Logger;

import org.construct_infrastructure.io.Message;
import org.construct_infrastructure.io.MessageReader;

import com.apple.dnssd.BrowseListener;
import com.apple.dnssd.DNSSD;
import com.apple.dnssd.DNSSDException;
import com.apple.dnssd.DNSSDService;
import org.construct_infrastructure.bonjourproxy.ServiceException;

/**
 * Client-side proxy object that can talk to a Construct discovery service, find services and
 * interact with them.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public class ProxyBonjourListener implements BrowseListener,
      ProxyBonjourContactResolvedListener {
   /**
    * The construct registration string.
    */
   public static final String BONJOUR_REGISTRATION_TYPE = "_construct._tcp";

   /**
    * The delay we will allow for the brows time when trying to connect.
    */
   private static final int BROWSE_DELAY = 10000;

   /**
    * The time period in ms between checks for construct nodes.
    */
   private static final int DELAY_RECHECK_INCRAMENT = 100;

   /**
    * The length of the &lt;/services&gt; tag.
    */
   private static final int SERVICES_END_TAG_LENGTH = 11;

   /**
    * The length of the &lt;services&gt; tag.
    */
   private static final int SERVICES_TAG_LENGTH = 10;

   /**
    * The set of construct instances we can see.
    */
   private final Map my_cInstances;

   /**
    * A lock for the contact set.
    */
   private final ReentrantLock my_contactsLock;

   /**
    * Are we browsing for bonjour contacts?
    */
   private final boolean my_isBrowsing;

   /**
    * The logger for this class.
    */
   private final Logger my_logger;

   /**
    * Creates a new instance of the listener and starts scanning for Construct instances.
    * 
    * @param a_logger
    *           where messages should be directed.
    * @throws DNSSDException
    *            if there is an error starting the browse operation.
    */
   public ProxyBonjourListener(final Logger a_logger) throws DNSSDException {
      my_logger = a_logger;
      my_isBrowsing = false;
      my_contactsLock = new ReentrantLock();
      my_cInstances = new HashMap();

      startBrowsing();
   }

   /**
    * Callback to notify when a contact has been resolved.
    * 
    * @see org.construct_infrastructure.bonjourproxy.ProxyBonjourContactResolvedListener#
    *      contactResolved(org.construct_infrastructure.bonjourproxy.ProxyBonjourContact)
    * @param a_contact
    *           The contact that was resolved.
    */
   public final void contactResolved(final ProxyBonjourContact a_contact) {
      try {
         my_contactsLock.lock();
         final String xmlServiceDescriptor = getXMLServiceDescriptors(a_contact);
         if (!my_cInstances.containsKey(a_contact) && (xmlServiceDescriptor != null)) {
            my_cInstances.put(a_contact, xmlServiceDescriptor);
         }
      } finally {
         my_contactsLock.unlock();
      }
   }

   /**
    * Attempts to get all service descriptors.
    * 
    * @throws InterruptedException
    *            if an error occurs while obtaining the contact lock.
    * @throws ServiceException
    *            if a service cannot be found.
    * @return all available services described in XML.
    */
   public final String getServiceDescriptors() throws InterruptedException, ServiceException {
      final StringBuffer output = new StringBuffer("<services>");
      // We first check to see if an instance of Construct is available
      // If not, we wait for delayed time to give the browse operation a chance.
      int time = BROWSE_DELAY;
      while (time > 0 && my_cInstances.isEmpty()) {
         synchronized (this) {
            try {
               wait(DELAY_RECHECK_INCRAMENT);
               time -= DELAY_RECHECK_INCRAMENT;
            } catch (InterruptedException ie) {
               my_logger.warning(ie.getMessage());
            }
         }
      }
      // Add all existing service descriptiors to the output
      // This invoves stripping the &lt;/services&gt; tags from each result and appending
      // it at the end
      try {
         my_contactsLock.lock();
         final Iterator iterator = my_cInstances.values().iterator();
         while (iterator.hasNext()) {
            final String descriptor = (String) iterator.next();
            // Remove tags
            if (descriptor != null && descriptor.startsWith("<services>")
                  && descriptor.endsWith("</services>")) {
               output.append(descriptor.substring(SERVICES_TAG_LENGTH, descriptor.length()
                     - SERVICES_END_TAG_LENGTH));
            }
         }
      } finally {
         my_contactsLock.unlock();
      }
      // Append end services tag
      output.append("</services>");
      return output.toString();
   }

   /**
    * Get the service descriptors in a big XML string.
    * 
    * @param a_bonjourContact
    *           the contact from which we wish to obtain service descriptors.
    * @return the XML form of the service descriptors (which could just be
    *         &lt;services>&lt;/services> or null if we are not connected to an instance of
    *         Construct
    */
   private String getXMLServiceDescriptors(final ProxyBonjourContact a_bonjourContact) {
      Socket toConstruct = null;
      String result = null;
      MessageReader messageReader = null;
      final ExecutorService executorService = Executors.newSingleThreadExecutor();
      try {
         toConstruct = new Socket(a_bonjourContact.getAddress(), a_bonjourContact.getPort());
         messageReader = new MessageReader(toConstruct.getInputStream(),
               executorService);
         // Process message from discovery service
         final Message message = messageReader.getMessage();
         result = message.getPayload();
      } catch (IOException ioe) {
         my_logger.info("IO Exception when trying to get service descriptor from: "
               + a_bonjourContact.getAddress() + ":" + a_bonjourContact.getPort());
      } catch (InterruptedException e) {
         my_logger.warning("InterruptedException occured while " + "reading message: "
               + e.getMessage());
      } catch (TimeoutException e) {
         my_logger.warning("TimeoutException while reading message: " + e.getMessage());
      } finally {
         try {
            if (messageReader != null) {
               messageReader.close();
            }
            if (toConstruct != null) {

               toConstruct.close();

            }
            if (executorService != null) {
               executorService.shutdown();
            }
         } catch (IOException e) {
            my_logger.warning("Could not close socket: " + e.getMessage());
         }
      }
      return result;
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
      my_logger.warning("Bonjour Operation failed: " + an_errorCode);
   }

   /**
    * Callback to notify when an error occurred during the resolve and the contact was not able
    * to be fully resolved.
    * 
    * @see org.construct_infrastructure.bonjourproxy.ProxyBonjourContactResolvedListener#resolveFailed(
    *      org.construct_infrastructure.bonjourproxy.ProxyBonjourContact, java.lang.String)
    * @param the_contact
    *           The contact which failed to resolve.
    * @param a_message
    *           A message detailing the error.
    */
   public final void resolveFailed(final ProxyBonjourContact the_contact,
         final String a_message) {
      my_logger.info("Service Resolution failed for: " + the_contact.toString() + " - "
            + a_message);
   }

   /**
    * The Browser invokes this callback when a service is discovered. If this service is not
    * already known to us (and is not us) we will add it to the contact list.
    * 
    * @param a_browser
    *           The active browse service.
    * @param the_flags
    *           Any flags: e.g. DNSSD.MORE_COMING.
    * @param an_ifIndex
    *           The interface the service was discovered on.
    * @param a_serviceName
    *           The services name.
    * @param a_regType
    *           The type of service.
    * @param a_domain
    *           The domain of the service.
    */
   public final void serviceFound(final DNSSDService a_browser, final int the_flags,
         final int an_ifIndex, final String a_serviceName, final String a_regType,
         final String a_domain) {
      final ProxyBonjourContact contact = new ProxyBonjourContact(a_serviceName, a_domain,
            a_regType, an_ifIndex);
      try {
         contact.resolve(this);
      } catch (DNSSDException e) {
         my_logger.info("Cannot resolve contact.\n" + e);
      }
   }

   /**
    * The Browser invokes this callback when a service is lost. If this service is known to us
    * we will remove it from the contact list.
    * 
    * @param a_browser
    *           The active browse service.
    * @param the_flags
    *           Any flags: e.g. DNSSD.MORE_COMING.
    * @param an_ifIndex
    *           The interface the service was discovered on.
    * @param a_serviceName
    *           The services name.
    * @param a_regType
    *           The type of service.
    * @param a_domain
    *           The domain of the service.
    */
   public final void serviceLost(final DNSSDService a_browser, final int the_flags,
         final int an_ifIndex, final String a_serviceName, final String a_regType,
         final String a_domain) {
      // Remove the service from our collection
      final ProxyBonjourContact contact = new ProxyBonjourContact(a_serviceName, a_domain,
            a_regType, an_ifIndex);
      try {
         my_contactsLock.lock();
         if (my_cInstances.containsKey(contact)) {
            my_cInstances.remove(contact);
         }
      } finally {
         my_contactsLock.unlock();
      }
   }

   /**
    * Start scanning for Construct Instances. Calling this method does not mean that you will
    * immediatly be connected to construct.
    * 
    * @throws DNSSDException
    *            if the browse operation fails.
    */
   private void startBrowsing() throws DNSSDException {
      if (!my_isBrowsing) {
         DNSSD.browse(0, 0, BONJOUR_REGISTRATION_TYPE, "", this);
      }
   }
}
