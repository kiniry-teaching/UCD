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
package org.construct_infrastructure.component.gossiping.membership;


import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Properties;
import java.util.Random;

import org.construct_infrastructure.component.AbstractConstructComponent;

/**
 * The simplest membership manager imaginable.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class MembershipManagerImpl extends AbstractConstructComponent implements
      MembershipManager {

   /**
    * Contacts are chosen at random: this is the random number generator we use.
    */
   private final Random my_rng;

   /**
    * The list of contacts.
    */
   private final List my_contacts;

   /**
    * Create the membership manager.
    * 
    * @param some_properties The properties for this component.
    */
   public MembershipManagerImpl(final Properties some_properties) {
      super();
      setProperties(some_properties);
      my_rng = new Random();
      my_contacts = Collections.synchronizedList(new ArrayList());
   }

   /**
    * This membership manager is so simple we don't keep track of contacts age
    * so this method does nothing.
    * 
    * @see org.construct_infrastructure.component.gossiping.membership.MembershipManager#ageContacts()
    */
   public final void ageContacts() {
      // do nothing
   }

   /**
    * Setup links to other components. This implementation of MembershipManager
    * does not rely on any other components.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#setupComponentLinks()
    */
   public final void setupComponentLinks() {
      // Empty method
   }

   /**
    * Template method called when the MembershipManager is started running.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#onRun()
    */
   public final void onRun() {
      // Empty method
   }

   /**
    * Template method called when the MemebershipManager is being shutdown.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#onShutdown()
    */
   public void onShutdown() {
      // Empty method
   }
   
   /**
    * React to a new contact being discovered.
    * 
    * @see org.construct_infrastructure.component.gossiping.membership.MembershipManager#
    *      contactDiscovered(org.construct_infrastructure.component.gossiping.membership.Contact)
    * @param a_contact
    *           The contact that was discovered.
    */
   public final void contactDiscovered(final Contact a_contact) {
      my_contacts.add(a_contact);
   }

   /**
    * React to a contact being lost.
    * 
    * @see org.construct_infrastructure.component.gossiping.membership.MembershipManager#
    *      contactLost(org.construct_infrastructure.component.gossiping.membership.Contact)
    * @param a_contact
    *           The contact that was lost.
    */
   public final void contactLost(final Contact a_contact) {
      my_contacts.remove(a_contact);
   }

   /**
    * Get the number of contacts that the manager knows about.
    * 
    * @see org.construct_infrastructure.component.gossiping.membership.MembershipManager#size()
    * @return The number of contacts in this list.
    */
   public final int size() {
      return my_contacts.size();
   }

   /**
    * Get a particular contact from the membership managers list.
    * 
    * @see org.construct_infrastructure.component.gossiping.membership.MembershipManager#
    *      getContact(int)
    * @param an_index
    *           The index of the contact to get.
    * @return The contact at that position in the list.
    * @throws IndexOutOfBoundsException
    *            if the index is out of range (index < 0 || index >= size()).
    */
   public final Contact getContact(final int an_index) throws IndexOutOfBoundsException {
      return (Contact) my_contacts.get(an_index);
   }

   /**
    * Recommend a contact to gossip with from the list of known contacts.
    * 
    * @see org.construct_infrastructure.component.gossiping.membership.MembershipManager#
    *      recommendContact()
    * @return The recommended contact or null if no contacts exist.
    */
   public final Contact recommendContact() {
      if (my_contacts.size() == 0) {
         return null;
      }
      return (Contact) my_contacts.get(my_rng.nextInt(my_contacts.size()));
   }

}
