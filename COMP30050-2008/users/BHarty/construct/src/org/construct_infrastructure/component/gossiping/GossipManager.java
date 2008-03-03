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
package org.construct_infrastructure.component.gossiping;

import org.construct_infrastructure.component.ConstructComponent;
import org.construct_infrastructure.component.gossiping.membership.Contact;

/**
 * The GossipManager provides a mechanism for disseminating a message to the
 * other construct nodes in the network and for notifying higher layers that a
 * message has arrived. The contents of a message are unspecified but nominally
 * contain a small fragment of RDF less than 64k in size.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public interface GossipManager extends ConstructComponent {

   /**
    * Disseminate a message around the network of construct nodes.
    * 
    * @param a_message
    *           The message to disseminate.
    */
   void gossipMessage(Message a_message);

   /**
    * Notification from the network manager that some gossip has been received
    * from the given source.
    * 
    * @param the_source
    *           The source of the gossip.
    * @param a_replyAddress
    *           The address of the contact to reply to, should a reply be
    *           required.
    * @param some_rawGossip
    *           The raw bytes received which represent the received message.
    */
   void receivedGossip(Contact the_source, Contact a_replyAddress, byte[] some_rawGossip);

}
