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
import java.util.logging.Logger;

import org.construct_infrastructure.component.datastorage.DataStoreManager;
import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.io.Protocol;

import com.hp.hpl.jena.query.QueryException;

/**
 * This class represents runnable persistent query objects. An object consists of a query
 * string, an ID and an outputstream for callbacks.
 * 
 * @author Adrian Clear (adrian.clear@ucd.ie)
 */
public class PersistentQuery implements Runnable {
   /**
    * The interface for the data store manager.
    */
   public static final String DSTORE_MANAGER 
      = "org.construct_infrastructure.component.datastorage.DataStoreManager";

   /**
    * This is used for logging in this Class.
    */
   private static final Logger LOGGER = Logger.getLogger(PersistentQuery.class.getName());
   
   /**
    * The query to be executed.
    */
   private final String my_query;

   /**
    * The unique query ID.
    */
   private final String my_queryID;

   /**
    * The ouputstream to send responses.
    */
   private final PrintStream my_outputStream;

   /**
    * The datastore manager that holds all the data that is queryable from this. QueryService
    */
   private transient DataStoreManager my_dataStoreManager;   

   /**
    * Persistent query constructor.
    * 
    * @param a_query
    *           the query.
    * @param a_queryID
    *           the query ID.
    * @param an_outputStream
    *           the outputstream used for callback.
    */
   public PersistentQuery(final String a_query, 
         final String a_queryID, final PrintStream an_outputStream) {
      my_query = a_query;
      my_queryID = a_queryID;
      my_outputStream = an_outputStream;
      try {
         my_dataStoreManager = (DataStoreManager) ComponentRegistry
               .getComponent(DSTORE_MANAGER);
      } catch (NoSuchComponentException e) {
         LOGGER.severe(e.getMessage());
      }
   }

   /**
    * The functionality of this thread.
    */
   public final void run() {
      String curr_result = null;
      try {
         curr_result = my_dataStoreManager.runQuery(my_query);
         if (curr_result != null) {
            my_outputStream.print(Protocol.format(my_queryID, curr_result,
                  Protocol.PERSISTENT_QUERY_RESPONSE));
         } else {
            my_outputStream.print(Protocol.format(my_queryID, "ERROR: " + "failed to execute query correctly",
                  Protocol.PERSISTENT_QUERY_RESPONSE));
         }
      } catch (QueryException e) {
         LOGGER.severe(e.getMessage());
      }
   }

   /**
    * Get the query string.
    * 
    * @return the query.
    */
   public final String getQuery() {
      return my_query;
   }

   /**
    * Get the query ID.
    * 
    * @return the query ID.
    */
   public final String getQueryID() {
      return my_queryID;
   }

   /**
    * Get the outputstream used to callback.
    * 
    * @return the outputstream.
    */
   public final PrintStream getOutputStream() {
      return my_outputStream;
   }
}
