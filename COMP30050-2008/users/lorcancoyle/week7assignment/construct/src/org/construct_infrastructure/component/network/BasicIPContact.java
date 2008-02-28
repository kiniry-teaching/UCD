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


/**
 * A basic IP contact which maintains an IP address and a port number.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class BasicIPContact implements IPContact {

   /**
    * The IP address of this contact.
    */
   private final InetAddress my_address;

   /**
    * The port number of this contact.
    */
   private final int my_port;

   /**
    * Create a basic IP contact which consists of simply an IP address and port
    * number.
    * 
    * @param an_address
    *           The IP address.
    * @param a_port
    *           The port number.
    */
   public BasicIPContact(final InetAddress an_address, final int a_port) {
      super();
      my_address = an_address;
      my_port = a_port;
   }

   /**
    * Get the IP address of this contact.
    * 
    * @see org.construct_infrastructure.component.network.IPContact#getAddress()
    * @return The IP address of this contact.
    */
   public final InetAddress getAddress() {
      return my_address;
   }

   /**
    * Get the port number of this contact.
    * 
    * @see org.construct_infrastructure.component.network.IPContact#getPort()
    * @return The port number of this contact.
    */
   public final int getPort() {
      return my_port;
   }

   /**
    * Determine whether this contact is equal to another.
    * 
    * @see java.lang.Object#equals(java.lang.Object)
    * @param a_contact
    *           The contact to compare with.
    * @return True is this contact is equal to the other.
    */
   public final boolean equals(final Object a_contact) {
      // GRAHAM: Consider rewriting this to avoid PMD warning
      if (!(a_contact instanceof BasicIPContact)) {
         return false;
      }
      final BasicIPContact other = (BasicIPContact) a_contact;
      return my_address.equals(other.my_address) && (my_port == other.my_port);
   }

   /**
    * Generate the hashcode for this contact.
    * 
    * @see java.lang.Object#hashCode()
    * @return The hashcode for this object.
    */
   public final int hashCode() {
      return my_address.hashCode() + my_port;
   }

   /**
    * Generate a string description of this contact.
    * 
    * @see java.lang.Object#toString()
    * @return A string description of this contact.
    */
   public final String toString() {
      return "[BasicIP:" + my_address + ":" + my_port + "]";
   }
}
