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
package org.construct_infrastructure.component.queryviewer;


import java.util.Properties;

import javax.swing.table.DefaultTableModel;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.component.datastorage.DataStoreManager;
import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;

/**
 * This component displays the data model that an instance of construct
 * currently holds.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class QueryViewerImpl extends AbstractConstructComponent implements QueryViewer {

   /**
    * The interface for the data store manager.
    */
   public static final String DSTORE_MANAGER
      = "org.construct_infrastructure.component.datastorage.DataStoreManager";

   /**
    * A link to the data store manager.
    */
   private DataStoreManager my_dataStoreManager;

   /**
    * The model viewer's panel for the gui.
    */
   private final QueryViewerPanel my_componentPanel;

   /**
    * The query that will be sent to construct - allows subsets of constructs
    * data to be displayed.
    */
   private String my_query = QueryViewerPanel.QUERY_ALL_DATA;

   /**
    * Create the model viewer component.
    * 
    * @param some_properties
    *           The properties for this component.
    */
   public QueryViewerImpl(final Properties some_properties) {
      super();
      setProperties(some_properties);
      my_componentPanel = new QueryViewerPanel(this);
      setGraphicalInterface(my_componentPanel);
   }

   /**
    * This method gets references to required components from the component
    * registry.
    * 
    * @throws NoSuchComponentException
    *            if an attempt is made to access a component which doesn't
    *            exist.
    */
   public final void setupComponentLinks() throws NoSuchComponentException {
      my_dataStoreManager = (DataStoreManager) ComponentRegistry.getComponent(DSTORE_MANAGER);
   }

   /**
    * Called when starting the model viewer.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#onRun()
    */
   public final void onRun() {
      // nothing to do
   }

   /**
    * Called when shutting down the model viewer.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#onShutdown()
    */
   public final void onShutdown() {
      // nothing to do
   }

   /**
    * Reset the model viewer data back to show nothing.
    */
   public final void reset() {
      my_componentPanel.setTableModel(new DefaultTableModel());
   }

   /**
    * Set the query that will be passed to construct. Does not check that the
    * query is well formed, valid or whatever.
    * 
    * @param a_query
    *           The query to use
    */
   public final void setQuery(final String a_query) {
      my_query = a_query;
      my_componentPanel.setTableModel(new DataStoreQueryTableModelAdaptor(this,
            my_dataStoreManager, my_query));
   }

   /**
    * Get the query string that is used to query construct.
    * 
    * @return Returns the query.
    */
   public final String getQuery() {
      return my_query;
   }

}
