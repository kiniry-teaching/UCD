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
package org.construct_infrastructure.component.dataport;

import org.construct_infrastructure.component.ConstructComponent;

/**
 * The data port interface defines a method that accepts RDF data formatted in N-TRIPLE format.
 * Implementing classes should parse this data and add it to the local data store.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public interface DataPort extends ConstructComponent {

   /**
    * The name used by the dataport to register with the discovery service.
    */
   String DP_NAME = "Construct DataPort";

   /**
    * Takes in a set of RDF statements in N-TRIPLE format to add to the data model. The form
    * N-TRIPLE (SPO.) + time-to-live (long) should be used where an explicit time-to-live value
    * is associated with the statements being passed in. The time should only be specified
    * after the last statement in the String, and will apply to all statements.
    * 
    * @param some_data
    *           The data to be added to the data store.
    * @return true if the data was added successfully, false otherwise.
    */
   boolean addData(String some_data);
}
