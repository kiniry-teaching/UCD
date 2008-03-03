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
package org.construct_infrastructure.component.datastorage;

import org.construct_infrastructure.component.ConstructComponent;
import org.construct_infrastructure.component.datastorage.observable.DataStoreObserver;

/**
 * This interface defines the methods available for accessing and retrieving data from the data
 * store. All access to the data store should be moderated by the DataManager in order that the
 * rules engine can be correctly maintained.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public interface DataStoreManager extends ConstructComponent {

   /**
    * Adds a set of RDF statements to the data store with the default expiry time.
    * 
    * @param some_statements
    *           RDF statements to be added in N-TRIPLE format.  
    * @param the_origin The origin of the data.        
    */
   void addStatements(String some_statements, Object the_origin);

   /**
    * Adds a set of RDF statements to the data store with a given expiry time.
    * 
    * @param some_statements
    *           A string containing RDF to be added in N-TRIPLE format.
    * @param an_expiryTime
    *           The time when the new statements should expire.
    * @param the_origin The origin of the data.
    */
   void addStatements(String some_statements, long an_expiryTime, Object the_origin);

   /**
    * Adds a set of RDF statements and metadata to the data store without notifying observers.
    * 
    * @param some_statements
    *           RDF statements to be added in N-TRIPLE format.
    * @param some_metadata
    *           meta data associated with the statements in N-TRIPLE format
    * @param the_origin The origin of the data.          
    */
   void addStatementsWithMetadata(String some_statements, String some_metadata, 
         Object the_origin);
  
   /**
    * This method iterates through all the statements in the data store and checks the
    * associated expiry date as given in the metadata. If the expiry data < now the statement
    * (and its metadata is deleted).
    */
   void removeAllExpiredStatements();
   
   /**
    * Get the expiry timer for the given statement.
    * 
    * @param a_statement
    *           The statement in N-TRIPLE format.
    * @return The current expiry timer count for the given statement or -1 if
    *         the statement does not exist.
    */
   long getStatementExpiryTimer(String a_statement);
   
   /**
    * Runs a query on the Datastore.
    * 
    * @param a_query
    *           the query to be run.
    * @return the results of the query as an array of strings in N-TRIPLE format.
    */
   String runQuery(String a_query);
  
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
   void addObserver(final DataStoreObserver an_observer)throws NullPointerException;

   /**
    * Deletes an observer from the set of observers of this object.
    * 
    * @param an_observer
    *           the observer to be deleted.
    */
   void deleteObserver(final DataStoreObserver an_observer);

}
