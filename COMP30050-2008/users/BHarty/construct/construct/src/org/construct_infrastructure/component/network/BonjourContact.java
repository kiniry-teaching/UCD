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
package org.construct_infrastructure.component.network;


import java.net.InetAddress;
import java.net.UnknownHostException;

import com.apple.dnssd.DNSSD;
import com.apple.dnssd.DNSSDException;
import com.apple.dnssd.DNSSDService;
import com.apple.dnssd.QueryListener;
import com.apple.dnssd.ResolveListener;
import com.apple.dnssd.TXTRecord;

/**
 * This class contains the information required to store, and resolve the
 * necessary details to set up a bonjour contact ready for gossiping.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public class BonjourContact implements ResolveListener, QueryListener, IPContact {

   /**
    * The nodeID of the target construct deployment.
    */
   private final String my_nodeID;

   /**
    * The domain on which the target service is registered on.
    */
   private final String my_domain;

   /**
    * The type of the service.
    */
   private final String my_type;

   /**
    * The iterface on which the service can be reached.
    */
   private final int my_ifIndex;

   /**
    * The address on which to contact the target construct deployment.
    */
   private InetAddress my_address;

   /**
    * The port on which to contact the target construct deployment.
    */
   private int my_port;

   /**
    * The listener to notify when this contact has been resolved.
    */
   private BonjourContactResolvedListener my_listener;

   /**
    * Creates a new BonjourContact object. Resolves the IP address and port
    * number of the named service.
    * 
    * @param a_nodeID
    *           The name of the target construct service.
    * @param a_domain
    *           The domain on which the target service is registered on.
    * @param a_type
    *           The type of the service.
    * @param an_ifIndex
    *           The iterface on which the service can be reached.
    */
   public BonjourContact(final String a_nodeID, final String a_domain, final String a_type,
         final int an_ifIndex) {
      // future JML fun: requires all parameters != null (for equals/hashcode)
      my_nodeID = a_nodeID;
      my_domain = a_domain;
      my_type = a_type;
      my_ifIndex = an_ifIndex;
   }

   /**
    * Resolve this bonjour contact to discover the IP address and port number
    * associated with the service.
    * 
    * @param a_listener
    *           The listener to notify when the service is resolved.
    * @throws DNSSDException
    *            if there is a problem resolving the IP and port number from the
    *            contact information.
    */
   public final void resolve(final BonjourContactResolvedListener a_listener)
      throws DNSSDException {
      my_listener = a_listener;
      DNSSD.resolve(0, my_ifIndex, my_nodeID, my_type, my_domain, this);
   }

   /**
    * Returns a string representation of this contact in the form
    * [BONJOUR:my_nodeID(my_address:my_port)].
    * 
    * @return a string representation of this contact.
    */
   public final String toString() {
      return "[BONJOUR:" + my_nodeID + "(" + my_address + ":" + my_port + ")]";
   }

   /**
    * Callback to this method invoked from resolve call in the constructor.
    * Allows us to get a handle on the port.
    * 
    * @param a_resolver
    *           The active resolver object.
    * @param the_flags
    *           Unused.
    * @param an_ifIndex
    *           The interface that the service can be reached on.
    * @param a_fullName
    *           The full service domain name.
    * @param an_hostName
    *           The target hostname of the machine providing the service.
    * @param a_port
    *           The port that the service listens on.
    * @param a_txtRecord
    *           The txt record associated with the service.
    */
   public final void serviceResolved(final DNSSDService a_resolver, final int the_flags,
         final int an_ifIndex, final String a_fullName, final String an_hostName,
         final int a_port, final TXTRecord a_txtRecord) {
      my_port = a_port;
      try {
         // Start a record query to obtain IP address from hostname
         DNSSD
               .queryRecord(0, an_ifIndex, an_hostName, 1 /* ns_t_a */, 1 /* ns_c_in */,
                     this);
      } catch (DNSSDException e) {
         my_listener.resolveFailed(this,
               "Could not resolve Contact IP address from hostname: " + an_hostName);
      }
      a_resolver.stop();
   }

   /**
    * Callback to this method invoked from query call in the serviceResolved
    * method. Allows us to get the IP address of the host.
    * 
    * @param a_query
    *           The active query object.
    * @param the_flags
    *           Any flags: e.g. DNSSD.MORE_COMING.
    * @param an_ifIndex
    *           The interface that the service can be reached on.
    * @param a_fullName
    *           The full service domain name.
    * @param an_rrtype
    *           The resource record's type.
    * @param an_rrclass
    *           The class of the resource record.
    * @param some_rdata
    *           The raw rdata of the resource record.
    * @param a_ttl
    *           The resource record's time to live, in seconds.
    */
   public final void queryAnswered(final DNSSDService a_query, final int the_flags,
         final int an_ifIndex, final String a_fullName, final int an_rrtype,
         final int an_rrclass, final byte[] some_rdata, final int a_ttl) {
      try {
         my_address = InetAddress.getByAddress(some_rdata);
         my_listener.contactResolved(this);
      } catch (UnknownHostException e) {
         my_listener.resolveFailed(this,
               "Unable to resolve IP address for Contact: bad address format.");
      }
   }

   /**
    * Called if an error occurs using service registration or the browse
    * request.
    * 
    * @param a_service
    *           the service invoking the callback.
    * @param the_errorCode
    *           the code representing the error that occured.
    */
   public final void operationFailed(final DNSSDService a_service, final int the_errorCode) {
      my_listener.resolveFailed(this,
            "Bonjour service reported error while resolving Contact IP address: Error #"
                  + Integer.toString(the_errorCode));
   }

   /**
    * Determine if this contact been sucessfully resolved.
    * 
    * @return True if this contact has been resolved to an IP address and port
    *         number.
    */
   public final boolean isResolved() {
      return (my_address != null);
   }

   /**
    * Returns the address that should be used to send a summary to this contact.
    * 
    * @return Returns the address.
    */
   public final InetAddress getAddress() {
      return my_address;
   }

   /**
    * Returns the port that should be used to send a summary to this contact.
    * 
    * @return Returns the port.
    */
   public final int getPort() {
      return my_port;
   }

   /**
    * Check if this contact is equal to another.
    * 
    * @see java.lang.Object#equals(Object)
    * @param a_contact
    *           The contact to compare with.
    * @return If this represents the same contact.
    */
   public final boolean equals(final Object a_contact) {
      // GRAHAM: Consider rewriting this to avoid PMD warning
      if (!(a_contact instanceof BonjourContact)) {
         return false;
      }
      final BonjourContact other = (BonjourContact) a_contact;
      return my_nodeID.equals(other.my_nodeID) && my_domain.equals(other.my_domain)
            && my_type.equals(other.my_type) && (my_ifIndex == other.my_ifIndex);
   }

   /**
    * Generate the hashcode of this contact.
    * 
    * @see java.lang.Object#hashCode()
    * @return The hashcode.
    */
   public final int hashCode() {
      return my_nodeID.hashCode() + my_domain.hashCode() + my_type.hashCode() + my_ifIndex;
   }
}
