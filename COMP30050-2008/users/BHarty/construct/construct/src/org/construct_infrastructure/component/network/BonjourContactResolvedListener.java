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

/**
 * Provides an interface for objects that wish to be notified when a
 * BonjourContact has been resolved.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public interface BonjourContactResolvedListener {

   /**
    * Callback to notify when a contact has been resolved.
    * 
    * @param the_contact
    *           The contact that was resolved.
    */
   void contactResolved(BonjourContact the_contact);

   /**
    * Callback to notify when an error occurred during the resolve and the
    * contact was not able to be fully resolved.
    * 
    * @param the_contact
    *           The contact which failed to resolve.
    * @param a_message
    *           A message detailing the error.
    */
   void resolveFailed(BonjourContact the_contact, String a_message);
}
