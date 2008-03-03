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
package org.construct_infrastructure.io;

import java.util.logging.Logger;

/**
 * An interface for a Socket associated with a Construct Service with associated logger.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public interface ServiceSocket extends Runnable {

   /**
    * is the socket closed?
    * 
    * @return true if the socket is closed, false otehrwise.
    */
   boolean isClosed();

   /**
    * Closes the socket when the object is shutdown.
    */
   void shutdown();

   /**
    * Returns the port on which this socket is listening.
    * 
    * @return the port number to which this socket is listening or -1 if the socket is not yet
    *         bound
    */
   int getLocalPort();

   /**
    * Return the logger associated with this service.
    * 
    * @return the logger associated with this service.
    */
   Logger getLogger();

}
