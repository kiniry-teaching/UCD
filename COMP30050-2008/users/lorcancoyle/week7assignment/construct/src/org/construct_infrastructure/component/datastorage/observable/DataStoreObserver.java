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
package org.construct_infrastructure.component.datastorage.observable;

/**
 * A class can implement the <code>DataStoreObserver</code> interface when it wants to be
 * informed of additions to the data store.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public interface DataStoreObserver {
   /**
    * This method is called whenever statements are added to the data store is changed.
    * 
    * @param a_mode
    *           Indicates whether a statement has been added or deleted as defined in the
    *           <code>ObservableDataStore</code> class
    * @param a_statement
    *           RDF statements that have been added to the data store in N-TRIPLE format. *
    * @param some_metadata
    *           RDF meta-data statements in N-TRIPLE format associated with the statements.
    * @param the_origin
    *           The origin of the data.
    *           
    * @see org.construct_infrastructure.component.datastorage.observable.ObservableDataStore
    */
   void update(final int a_mode, String a_statement, String some_metadata, Object the_origin);
}
