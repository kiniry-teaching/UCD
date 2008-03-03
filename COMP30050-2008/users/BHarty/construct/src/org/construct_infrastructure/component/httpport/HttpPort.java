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
package org.construct_infrastructure.component.httpport;

import org.construct_infrastructure.component.ConstructComponent;

/**
 * The HttpPort is an open socket that accepts HTTP GET requests and returns all the data in
 * Construct. It will take POST requests which contain SPARQL queries and return their results
 * or some failure code if the query is malformed.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 */
public interface HttpPort extends ConstructComponent {

   /**
    * The name used by the httpport to register with the discovery service.
    */
   String HP_NAME = "Construct HttpPort";

   /**
    * Takes in an HTTP request, checks to see what type it is (GET or POST) and handles it
    * appropriately. If the request is a GET then all construct data is sent back. If the
    * request is a post then the data in the post is treated as a SPARQL query and executed.
    * 
    * @param a_request
    *           The data to be added to the data store.
    * @return the response from handling the request. This will typically be a bunch of RDF
    *         statements or an error if the SPARQL query was malformed
    */
   String handleRequest(String a_request);
}
