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


import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import javax.swing.table.AbstractTableModel;

import org.construct_infrastructure.component.datastorage.DataStoreManager;
import org.construct_infrastructure.component.datastorage.observable.DataStoreObserver;

import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.query.ResultSetFactory;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;

/**
 * An adaptor to use the datastore as the backing for a table model and display
 * the results of running a given query against it.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class DataStoreQueryTableModelAdaptor extends AbstractTableModel implements
      DataStoreObserver {

   /**
    * Serial version id.
    */
   private static final long serialVersionUID = 1L;

   /**
    * The contents of the datastore in a convenient random access fashion.
    */
   private List my_modelData;

   /**
    * The column headers for the display.
    */
   private List my_columnHeaders;

   /**
    * The datastore that backs this table model.
    */
   private DataStoreManager my_datastore;

   /**
    * The modelviewer this table model belongs to.
    */
   private QueryViewer my_parent;

   /**
    * The query to run against the data store.
    */
   private String my_query;

   /**
    * Create an adaptor which allows the results of a query on the given
    * datastore to be shown in a JTable.
    * 
    * @param a_parent
    *           The modelviewer this table model belongs to.
    * @param a_datastore
    *           The datastore to adapt
    * @param a_query
    *           The query to run against the data store.
    */
   public DataStoreQueryTableModelAdaptor(final QueryViewer a_parent,
         final DataStoreManager a_datastore, final String a_query) {
      super();
      my_parent = a_parent;
      my_query = a_query;
      my_datastore = a_datastore;
//      my_datastore.addObserver(this);
      my_modelData = createStatementList(a_datastore, a_query);
   }

   /**
    * Create a random access List of statments from the datastore.
    * 
    * @param a_datastore
    *           The datastore to list
    * @param a_query
    *           The query to run on the datastore
    * @return a sequence of statements in a List
    */
   private List createStatementList(final DataStoreManager a_datastore, final String a_query) {
      final String data = a_datastore.runQuery(a_query);
      final Model model = ModelFactory.createDefaultModel();
      model.read(new ByteArrayInputStream(data.getBytes()), null, "N-TRIPLE");
      final ResultSet results = ResultSetFactory.fromRDF(model);
      my_columnHeaders = results.getResultVars();
      final List theList = new ArrayList();
      while (results.hasNext()) {
         final QuerySolution solution = results.nextSolution();
         final Map rowInfo = new Hashtable();
         final Iterator iterator = solution.varNames();
         while (iterator.hasNext()) {
            final String variable = (String) iterator.next();
            rowInfo.put(variable, solution.get(variable));
         }
         theList.add(rowInfo);
      }
      return theList;
   }

   /**
    * There's one row per statement.
    * 
    * @see javax.swing.table.TableModel#getRowCount()
    * @return the number of rows.
    */
   public final int getRowCount() {
      return my_modelData.size();
   }

   /**
    * Get the number of columns in this table model.
    * 
    * @see javax.swing.table.TableModel#getColumnCount()
    * @return the number of columns.
    */
   public final int getColumnCount() {
      return my_columnHeaders.size();
   }

   /**
    * Get the name of each column...
    * 
    * @see javax.swing.table.TableModel#getColumnName(int)
    * @param a_column
    *           the index of the column to get the header for.
    * @return the header name for each column.
    */
   public final String getColumnName(final int a_column) {
      return (String) my_columnHeaders.get(a_column);
   }

   /**
    * Perform the translation between the datastore and the values. Get the
    * value at the position given by rowIndex and columnIndex in the table.
    * 
    * @see javax.swing.table.TableModel#getValueAt(int, int)
    * @param a_rowIndex
    *           the row in the table.
    * @param a_columnIndex
    *           the column in the table.
    * @return the value at a particular position in the table.
    */
   public final Object getValueAt(final int a_rowIndex, final int a_columnIndex) {
      final Map table = (Map) my_modelData.get(a_rowIndex);
      return table.get(my_columnHeaders.get(a_columnIndex));
   }

   /**
    * This method is called whenever the data store is changed.
    * 
    * @param a_mode
    *           Indicates whether a statement has been added or deleted
    * @param a_statement
    *           RDF statements that have been added to the data store in
    *           N-TRIPLE format.
    * @param some_metadata
    *           RDF meta-data statements in N-TRIPLE format associated with the
    *           statements.
    * @param the_origin
    *           The origin of the data.
    * 
    * @see org.construct_infrastructure.component.datastorage.observable.DataStoreObserver#update(int,
    *      java.lang.String, java.lang.String)
    */
   public final void update(final int a_mode, final String a_statement,
         final String some_metadata, final Object the_origin) {
      my_parent.getLogger().finest("Statement changed: " + a_statement);
      my_modelData = createStatementList(my_datastore, my_query);
      fireTableDataChanged();
   }

}
