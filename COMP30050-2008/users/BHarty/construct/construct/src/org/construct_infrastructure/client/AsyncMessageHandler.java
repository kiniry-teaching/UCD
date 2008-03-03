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
package org.construct_infrastructure.client;

import org.construct_infrastructure.io.Message;

/**
 * This intefaces defines a method that is called when an asynchronous message is received.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public interface AsyncMessageHandler {

   /**
    * This method handles asynchronous messages received from Construct.
    * 
    * @param a_message
    *           the message received
    */
   void onMessage(Message a_message);
   
   /**
    * This method handles error messages raised during processing of asynchronous messages.
    * Currently, this only involves logging.
    * 
    * @param an_exception
    *           the error raised when handing an asynchronous message.
    */
   void onError(final Exception an_exception);

}
