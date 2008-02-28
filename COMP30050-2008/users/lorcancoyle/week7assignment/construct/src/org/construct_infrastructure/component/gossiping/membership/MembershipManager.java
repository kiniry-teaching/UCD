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

import org.construct_infrastructure.component.ConstructComponent;

/**
 * The MembershipManager component keeps track of a list of Contacts with which
 * to gossip.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public interface MembershipManager extends ConstructComponent {

   /**
    * Age the contacts in the membership list. Could be used as an indicator for
    * choosing between contacts to remove from the list.
    */
   void ageContacts();

   /**
    * This method should be called to notify the membership manager that a new
    * process has been discovered.
    * 
    * @param a_contact
    *           The contact discovered.
    */
   void contactDiscovered(Contact a_contact);

   /**
    * This method should be called to notify the membership manager that it has
    * been detected that a contact has been lost.
    * 
    * @param a_contact
    *           The contact that has been lost.
    */
   void contactLost(Contact a_contact);

   /**
    * Get the number of contacts that the manager knows about.
    * 
    * @return The number of contacts in this list.
    */
   int size();

   /**
    * Get a particular contact from the membership managers list.
    * 
    * @param an_index
    *           The index of the contact to get.
    * @return The contact at that position in the list.
    */
   Contact getContact(int an_index);

   /**
    * Recommend a contact to gossip with from the list of known contacts.
    * 
    * @return The recommended contact or null if no contacts exist.
    */
   Contact recommendContact();
   // GRAHAM: Allow more than one contact to be recommended.
   // recommendContact: We give the responsibility of choosing which contact to
   // gossip with to the membership manager because it is in a unique position
   // to record various metadata about contacts, when they were last gossiped
   // with etc. and can use this metadata to select a node more intelligently
   // (although for the moment, random will do!).

}
