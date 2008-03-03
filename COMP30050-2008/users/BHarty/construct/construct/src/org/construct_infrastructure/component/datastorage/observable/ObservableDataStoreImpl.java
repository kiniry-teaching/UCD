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


import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.apache.commons.lang.StringEscapeUtils;
import org.construct_infrastructure.loader.ConstructProperties;

import com.hp.hpl.jena.rdf.model.Statement;

/**
 * This class represents an observable view of the data store and provides notifacations when
 * new data is added.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public class ObservableDataStoreImpl implements ObservableDataStore {

   /**
    * This class will update an observer of the data store when a new statement is added or
    * removed. The ObservableDataStoreImpl class starts new instances of this class as
    * required.
    * 
    * @author Graeme Stevenson
    */
   class NotifyThread implements Runnable {
      /**
       * Meta data associated with the statement.
       */
      private final String my_metaData;

      /**
       * Whether the statement is being added or deleted.
       */
      private final int my_mode;

      /**
       * The observer to be notified.
       */
      private final DataStoreObserver my_observer;

      /**
       * The origin of the update.
       */
      private final Object my_origin;

      /**
       * The statement about which we are notifying.
       */
      private final String my_statement;

      /**
       * Create a new Thread that will notify an observer of the data store of a change in
       * state.
       * 
       * @param an_observer
       *           the observer we must notify.
       * @param a_mode
       *           whether data has been added or removed.
       * @param a_statement
       *           the statement associated with the update.
       * @param some_metadata
       *           the metadata associated with the statement. This value will be null if the
       *           statment is being deleted.
       * @param the_origin
       *           of the update. This value will be null if the statment is being deleted.
       */
      public NotifyThread(final DataStoreObserver an_observer, final int a_mode,
            final String a_statement, final String some_metadata, final Object the_origin) {
         my_observer = an_observer;
         my_mode = a_mode;
         my_statement = a_statement;
         my_metaData = some_metadata;
         my_origin = the_origin;
      }

      /**
       * Update the observer.
       */
      public void run() {
         my_observer.update(my_mode, my_statement, my_metaData, my_origin);
      }
   }

   /**
    * The logger for this class.
    */
   private static final Logger MY_LOGGER = Logger
         .getLogger("org.construct_infrastructure.component.datastorage.observable");

   /**
    * A vector containing the observers of the data store.
    */
   private final List my_observers;

   /**
    * The executor that performs the required notifications.
    */
   private final transient ExecutorService my_executor;

   /**
    * Construct an ObservableDataStore with zero Observers.
    */
   public ObservableDataStoreImpl() {
      MY_LOGGER.setLevel(Level.parse(ConstructProperties.getLoggingLevel()));
      my_observers = new ArrayList();
      // Use thread cache
      my_executor = Executors.newSingleThreadExecutor();
   }

   /**
    * Adds an observer to the set of observers for this object, provided that it is not the
    * same as some observer already in the set. The order in which notifications will be
    * delivered to multiple observers is not specified. See the class comment.
    * 
    * @param an_observer
    *           an observer to be added.
    * @throws IllegalArgumentException
    *            if the parameter an_observer is null.
    */
   public final synchronized void addObserver(final DataStoreObserver an_observer)
      throws IllegalArgumentException {
      if (an_observer == null) {
         throw new IllegalArgumentException();
      }
      if (!my_observers.contains(an_observer)) {
         my_observers.add(an_observer);
      }
   }

   /**
    * Returns the number of observers of this <tt>Observable</tt> object.
    * 
    * @return the number of observers of this object.
    */
   public final synchronized int countObservers() {
      return my_observers.size();
   }

   /**
    * Deletes an observer from the set of observers of this object.
    * 
    * @param an_observer
    *           the observer to be deleted.
    */
   public final synchronized void deleteObserver(final DataStoreObserver an_observer) {
      my_observers.remove((Object) an_observer);
   }

   /**
    * This method should be called by the DataStoreManager when new statements are being added
    * to the data store. A statement cannot be null, although metadata can.
    * 
    * @param a_mode
    *           Indicates whether a statement has been added or deleted.
    * @param a_statement
    *           RDF statements that have been added to the data store in N-TRIPLE format. *
    * @param some_metadata
    *           RDF meta-data statements in N-TRIPLE format associated with the statements.
    * @param the_origin
    *           The origin of the data.
    * @throws IllegalArgumentException
    *            if the parameter a_statement is null.
    */
   public final void notifyObservers(final int a_mode, final Statement a_statement,
         final Statement[] some_metadata, final Object the_origin)
      throws IllegalArgumentException {

      // Cannot have a null statement
      if (a_statement == null) {
         throw new IllegalArgumentException("Statement cannot be null");
      }

      // Convert the Statement to N-TRIPLE.
      final String statementNTriple = stmtToNTriple(a_statement);
      // Convert the meta-data to N-TRIPLE if it is non-null.
      final StringBuffer stmtMetaData = new StringBuffer();
      if (some_metadata != null) {
         for (int i = 0; i < some_metadata.length; i++) {
            stmtMetaData.append(stmtToNTriple(some_metadata[i]));
         }
      }

      // a temporary array buffer, used as a snapshot of the state of current Observers.
      final Object[] arrLocal = my_observers.toArray();

      // Iterate through the observers and notify them.
      synchronized (this) {
         for (int i = arrLocal.length - 1; i >= 0; i--) {
            my_executor.execute(new NotifyThread((DataStoreObserver) arrLocal[i], a_mode,
                  statementNTriple, stmtMetaData.toString(), the_origin));

         }
      }
   }

   /**
    * Converts a statement to N-TRIPLE format.
    * 
    * @param a_statement
    *           The Jena Statement to be converted to N-TRIPLE format.
    * @return a N-TRIPLE encoded String representing the input Statement
    */
   private String stmtToNTriple(final Statement a_statement) {
      final StringBuffer stringBuffer = new StringBuffer("<");
      stringBuffer.append(StringEscapeUtils.escapeJava(a_statement.getSubject().toString()));
      stringBuffer.append("> <");
      stringBuffer.append(StringEscapeUtils.escapeJava(a_statement.getPredicate().toString()));
      stringBuffer.append("> ");
      if (a_statement.getObject().isLiteral()) {
         stringBuffer.append('\"');
         stringBuffer.append(StringEscapeUtils.escapeJava(a_statement.getObject().toString()));
         stringBuffer.append("\" . ");
      } else {
         stringBuffer.append('<');
         stringBuffer.append(StringEscapeUtils.escapeJava(a_statement.getObject().toString()));
         stringBuffer.append("> . ");
      }
      return stringBuffer.toString();
   }

}
