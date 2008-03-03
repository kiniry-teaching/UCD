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
package org.construct_infrastructure.component.persistentqueryservice;

import java.io.PrintStream;

import org.construct_infrastructure.component.ConstructComponent;


/**
 * This class defines the operations which a persistent query service should implement. A
 * persistent query service is a query service which accepts queries and executes them
 * asynchonously and continuously every minute. The queries are executed in a round-robin
 * fashion and may be cancelled at any time.
 * 
 * @author Adrian Clear (adrian.clear@ucd.ie)
 */
public interface PersistentQueryService extends ConstructComponent {
   /**
    * The name used by the persistent query service to register with the discovery service.
    */
   String PQS_NAME = "Construct PersistentQueryService";

   /**
    * Adds a query for asynchronous execution.
    * 
    * @param the_query
    *           the query string
    * @param the_queryID
    *           the unique id for the query
    * @param the_outputStream
    *           the output stream for callbacks
    */
   void query(final String the_query, final String the_queryID,
         final PrintStream the_outputStream);

   /**
    * Remove a query from asynchronous execution.
    * 
    * @param the_queryID
    *           the unique id of the query
    */
   void cancelQuery(final String the_queryID);
}
