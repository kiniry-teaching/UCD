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

import com.hp.hpl.jena.rdf.model.Statement;

/**
 * An Observable view of the data store.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public interface ObservableDataStore {

   /**
    * Constant representing an addition to the data store.
    */
   int ADDED = 0;

   /**
    * Constant representing removal from the data store.
    */
   int REMOVED = 1;

   /**
    * Adds an observer to the set of observers for this object, provided that it is not the
    * same as some observer already in the set. The order in which notifications will be
    * delivered to multiple observers is not specified. See the class comment.
    * 
    * @param an_observer
    *           an observer to be added.
    * @throws NullPointerException
    *            if the parameter o is null.
    */
   void addObserver(final DataStoreObserver an_observer) throws NullPointerException;

   /**
    * Deletes an observer from the set of observers of this object.
    * 
    * @param an_observer
    *           the observer to be deleted.
    */
   void deleteObserver(final DataStoreObserver an_observer);

   /**
    * This method should be called by the DataStoreManager when new statements are being added
    * to the data store.
    * 
    * @param a_mode
    *           Indicates whether a statement has been added or deleted
    * @param a_statement
    *           RDF statements that have been added to the data store in N-TRIPLE format. *
    * @param some_metadata
    *           RDF meta-data statements in N-TRIPLE format associated with the statements. *
    * @param the_origin
    *           The origin of the data.
    */
   void notifyObservers(int a_mode, final Statement a_statement,
         final Statement[] some_metadata, final Object the_origin);

   /**
    * Returns the number of observers of this <tt>Observable</tt> object.
    * 
    * @return the number of observers of this object.
    */
   int countObservers();

}
