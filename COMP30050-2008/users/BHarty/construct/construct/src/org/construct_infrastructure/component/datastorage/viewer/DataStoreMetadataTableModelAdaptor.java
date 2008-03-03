//
// $Revision: 7810 $: $Date: 2008-02-20 17:51:52 +0000 (Wed, 20 Feb 2008) $ - $Author: gstevenson $
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
package org.construct_infrastructure.component.datastorage.viewer;


import java.io.ByteArrayInputStream;
import java.io.UnsupportedEncodingException;
import java.net.URLEncoder;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import javax.swing.table.AbstractTableModel;

import org.construct_infrastructure.component.datastorage.DataStoreManager;
import org.construct_infrastructure.component.datastorage.MetaData;
import org.construct_infrastructure.component.datastorage.observable.DataStoreObserver;
import org.construct_infrastructure.component.datastorage.observable.ObservableDataStore;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.RDFNode;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.Statement;
import com.hp.hpl.jena.rdf.model.StmtIterator;
import com.hp.hpl.jena.shared.Lock;

/**
 * An adaptor to use the datastore as the backing for a table model and show the
 * metadata where possible.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class DataStoreMetadataTableModelAdaptor extends AbstractTableModel implements
      DataStoreObserver {

   /**
    * Column header for the subject column.
    */
   public static final String SUBJECT_COLUMN = "subject";

   /**
    * Column header for the predicate column.
    */
   public static final String PREDICATE_COLUMN = "predicate";

   /**
    * Column header for the object column.
    */
   public static final String OBJECT_COLUMN = "object";

   /**
    * Column header for the expiry timer column.
    */
   public static final String EXPIRY_COLUMN = "expiry timer";

   /**
    * Column header for the origin column.
    */
   public static final String ORIGIN_COLUMN = "origin";

   /**
    * Serial version id.
    */
   private static final long serialVersionUID = 1L;

   /**
    * The contents of the datastore in a convenient random access fashion.
    */
   private final List my_modelData;

   /**
    * The column headers for the display.
    */
   private final List my_columnHeaders;

   /**
    * The datastore that backs this table model.
    */
   private final DataStoreManager my_datastore;

   /**
    * The model that the datastore uses.
    */
   private final Model my_model;

   /**
    * The metadata model that the datastore uses.
    */
   private final Model my_metadata;

   /**
    * The lock controlling access to the table data.
    */
   private final ReentrantReadWriteLock my_lock;

   /**
    * Create an adaptor which allows the data store to be shown in a JTable.
    * 
    * @param a_datastore
    *           The datastore to adapt.
    * @param the_model
    *           The model to show in the table.
    * @param the_metadata
    *           The metadata to show in the table.
    */
   public DataStoreMetadataTableModelAdaptor(final DataStoreManager a_datastore,
         final Model the_model, final Model the_metadata) {
      super();
      my_lock = new ReentrantReadWriteLock();
      my_model = the_model;
      my_metadata = the_metadata;
      my_datastore = a_datastore;
      my_datastore.addObserver(this);
      my_columnHeaders = createDefaultHeader();
      my_modelData = createStatementList(my_model, my_metadata, "unavailable");
   }

   /**
    * Create a default header for the display of the model.
    * 
    * @return A default header containing subject, predicate, object labels
    */
   private List createDefaultHeader() {
      final List header = new ArrayList();
      header.add(SUBJECT_COLUMN);
      header.add(PREDICATE_COLUMN);
      header.add(OBJECT_COLUMN);
      header.add(EXPIRY_COLUMN);
      header.add(ORIGIN_COLUMN);
      return header;
   }

   /**
    * Create a random access List of row data from the given Jena models.
    * 
    * @param a_model
    *           The model to list
    * @param some_metadata
    *           The associated metadata
    * @param the_origin
    *           The origin of the data
    * @return a sequence of statements in a List
    */
   private List createStatementList(final Model a_model, final Model some_metadata,
         final Object the_origin) {
      a_model.enterCriticalSection(Lock.READ);
      some_metadata.enterCriticalSection(Lock.READ);

      final List theList = new ArrayList();
      try {
         final StmtIterator iterator = a_model.listStatements();
         while (iterator.hasNext()) {
            final Statement statement = iterator.nextStatement();
            theList.add(new RowData(statement, getStatementExpiryTimer(statement,
                  some_metadata), the_origin));
         }
      } finally {
         a_model.leaveCriticalSection();
         some_metadata.leaveCriticalSection();
      }
      return theList;
   }

   /**
    * Get the expiry timer for the given statement. The metadata model must be
    * locked for reading before calling this method.
    * 
    * @param a_statement
    *           The statement to look for an expiry timer for.
    * @param the_metadata
    *           The model that contains the metadata for the given statement.
    * @return The expiry timer for the given statement or "unavailable" if not
    *         found.
    */
   private String getStatementExpiryTimer(final Statement a_statement,
         final Model the_metadata) {
      long expiryTimer = -1;

      final String statementGUID = constructStmtGuid(a_statement.getSubject(), a_statement
            .getPredicate(), a_statement.getObject());

      // find its metadata
      final Resource metaDataResource = the_metadata.getResource(MetaData.SUBJECT_PREFIX
            + statementGUID);
      final Statement propertyStatement = metaDataResource
            .getProperty(MetaData.EXPIRY_COUNTDOWN);

      // if the expiry timer exists, convert it to a long for return
      if (propertyStatement != null) {
         final String expiryTimerString = propertyStatement.getObject().toString();
         expiryTimer = Long.parseLong(expiryTimerString);
      }

      return (expiryTimer == -1) ? "unavailable" : Long.toString(expiryTimer);
   }

   /**
    * This method constructs a meta-ID from the parts of a Statement.
    * 
    * @param a_subject
    *           the subject we are interested in.
    * @param a_predicate
    *           the predicate linking the subject and object.
    * @param an_object
    *           the object we are interested in.
    * @return the meta-id for the given Statement.
    */
   private String constructStmtGuid(final Resource a_subject, final Property a_predicate,
         final RDFNode an_object) {
      String result = "";
      try {
         result = URLEncoder.encode((a_subject.toString() + a_predicate.toString() + an_object
               .toString()), "UTF-8");
      } catch (UnsupportedEncodingException an_exception) {
        an_exception.printStackTrace();
      }
      return result;
      // return (a_subject.toString() + "@" + a_predicate.toString() + "@" +
      // an_object.toString())
      // .replace('#', '$');
   }

   /**
    * There's one row per statement.
    * 
    * @see javax.swing.table.TableModel#getRowCount()
    * @return the number of rows.
    */
   public final int getRowCount() {
      int count = 0;
      try {
         my_lock.readLock().lock();
         count = my_modelData.size();
      } finally {
         my_lock.readLock().unlock();
      }
      return count;
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
    * Get the name of each column.
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
      String value = null;
      try {
         my_lock.readLock().lock();
         if (a_rowIndex < my_modelData.size()) {
            final RowData row = (RowData) my_modelData.get(a_rowIndex);
            final String column = (String) my_columnHeaders.get(a_columnIndex);
            if (SUBJECT_COLUMN.equals(column)) {
               value = row.getSubject();
            } else if (PREDICATE_COLUMN.equals(column)) {
               value = row.getPredicate();
            } else if (OBJECT_COLUMN.equals(column)) {
               value = row.getObject();
            } else if (EXPIRY_COLUMN.equals(column)) {
               value = row.getExpiry();
            } else if (ORIGIN_COLUMN.equals(column)) {
               value = row.getOrigin();
            }
         }
      } finally {
         my_lock.readLock().unlock();
      }

      return value;
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
    * @see org.construct_infrastructure.component.datastorage.observable.DataStoreObserver#update(int,
    *      java.lang.String, java.lang.String)
    */
   public final void update(final int a_mode, final String a_statement,
         final String some_metadata, final Object the_origin) {
      //try {
      // Create a list of the statements from the given update
      final Model model = ModelFactory.createDefaultModel();
      model.read(new ByteArrayInputStream(a_statement.getBytes()), null, "N-TRIPLE");
      final Model metadata = ModelFactory.createDefaultModel();
      metadata.read(new ByteArrayInputStream(some_metadata.getBytes()), null, "N-TRIPLE");
      final List statements = createStatementList(model, metadata, the_origin);

      // Then add or remove it...
      try {
         my_lock.writeLock().lock();
         if (a_mode == ObservableDataStore.ADDED) {
            my_modelData.addAll(statements);
         } else if (a_mode == ObservableDataStore.REMOVED) {
            my_modelData.removeAll(statements);
         } else {
            my_datastore.getLogger().warning(
                  "Unknown update type received from datastore: " + a_mode);
         }
      } finally {
         my_lock.writeLock().unlock();
      }
      fireTableDataChanged();
      //} catch (RuntimeException e) {
      //   System.err.println("Statement: " + a_statement + "\nMetadata: " +
      // some_metadata);
      //   e.printStackTrace();
      //   throw e;
      //}
   }

   /**
    * Refresh the view in the table.
    */
   public final void refresh() {
      try {
         my_lock.writeLock().lock();
         my_metadata.enterCriticalSection(Lock.READ);
         final Iterator iterator = my_modelData.iterator();
         while (iterator.hasNext()) {
            final RowData row = (RowData) iterator.next();
            row.setExpiry(getStatementExpiryTimer(row.getStatement(), my_metadata));
         }
      } finally {
         my_lock.writeLock().unlock();
         my_metadata.leaveCriticalSection();
      }
      fireTableDataChanged();
   }

   /**
    * This class stores information for a single row in the table.
    * 
    * @author Graham Williamson (graham.williamson@ucd.ie)
    */
   private class RowData {

      /**
       * The statement shown in this row.
       */
      private final Statement my_statement;

      /**
       * The expiry timer for that statement.
       */
      private String my_expiry;

      /**
       * The origin for the statement.
       */
      private final Object my_origin;

      /**
       * Create a new row data.
       * 
       * @param a_statement
       *           The statement in this row.
       * @param the_expiry
       *           The expiry timer for that statement.
       * @param the_origin
       *           The origin for the statement.
       */
      public RowData(final Statement a_statement, final String the_expiry,
            final Object the_origin) {
         super();
         my_statement = a_statement;
         my_expiry = the_expiry;
         my_origin = the_origin;
      }

      /**
       * Get the statement this row is displaying.
       * 
       * @return The statement.
       */
      public final Statement getStatement() {
         return my_statement;
      }

      /**
       * Get the subject to display for this row.
       * 
       * @return The subject.
       */
      public final String getSubject() {
         return my_statement.getSubject().toString();
      }

      /**
       * Get the predicate to display for this row.
       * 
       * @return The predicate.
       */
      public final String getPredicate() {
         return my_statement.getPredicate().toString();
      }

      /**
       * Get the object to display for this row.
       * 
       * @return The object.
       */
      public final String getObject() {
         return my_statement.getObject().toString();
      }

      /**
       * Get the origin for this row.
       * 
       * @return The origin for this row.
       */
      public final String getOrigin() {
         return (my_origin == null) ? "null" : my_origin.toString();
      }

      /**
       * Get the expiry timer to display for this row.
       * 
       * @return The expiry timer.
       */
      public final String getExpiry() {
         return my_expiry;
      }

      /**
       * Set the expiry timer to display for this row.
       * 
       * @param the_expiry
       *           The expiry timer to display for this row.
       */
      public final void setExpiry(final String the_expiry) {
         my_expiry = the_expiry;
      }

      /**
       * Test if this row represents the same statement as another.
       * 
       * @param an_object
       *           The object to compare with.
       * @return If this row represents the same row as another.
       * @see java.lang.Object#equals(java.lang.Object)
       */
      public final boolean equals(final Object an_object) {
         if (!(an_object instanceof RowData)) {
            return false;
         }
         final RowData other = (RowData) an_object;
         return my_statement.equals(other.my_statement);
      }

      /**
       * Get the hashcode for this row data.
       * 
       * @return The hashcode for this row data.
       * @see java.lang.Object#hashCode()
       */
      public final int hashCode() {
         return my_statement.hashCode();
      }

   }

}