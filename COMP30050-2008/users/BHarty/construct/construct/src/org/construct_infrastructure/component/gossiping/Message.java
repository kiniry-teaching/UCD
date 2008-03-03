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

/**
 * Represents a message which can be disseminated around the network via
 * gossiping.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public interface Message {

   /**
    * Serialize the message to a string of bytes.
    * 
    * @return The message represented as a byte array.
    */
   byte[] serialize();

   /**
    * Get the message ID of this message.
    * 
    * @return The message ID of this message.
    */
   MessageID getMessageID();

   /**
    * Get the time that this message was created.
    * 
    * @return The time this message was created.
    */
   long getTime();
}
