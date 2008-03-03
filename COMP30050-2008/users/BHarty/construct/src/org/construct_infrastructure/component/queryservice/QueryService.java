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
package org.construct_infrastructure.component.queryservice;

import org.construct_infrastructure.component.ConstructComponent;

/**
 * This class defines the operations which a query service should implement in
 * order to query a data source synchronously.
 * 
 * @author Lorcan Coyle (lorcan.coyle@ucd.ie)
 */
public interface QueryService extends ConstructComponent {
   /**
    * The name used by the queryservice to register with the discovery service.
    */
   public static final String QS_NAME = "Construct QueryService";
   
   
   /**
    * Adds new data into the data model.
    * 
    * @param the_data
    *            the new data to be added.
    * @param the_expiryTime
    *            the time when the statements in the provided model should
    *            expire. <code>
    * <JML>
    * requires the_data != null; 
    * requires the_expiryTime > 0;
    * </JML>
    * </code>
    */   
   String synchronousQuery(String the_query);
      
}
