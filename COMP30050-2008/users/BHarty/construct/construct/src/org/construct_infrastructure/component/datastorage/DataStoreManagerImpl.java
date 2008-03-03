//
// $Revision: 7870 $: $Date: 2008-02-25 15:06:14 +0000 (Mon, 25 Feb 2008) $ - $Author:
// gstevenson $
//
// This file is part of Construct, a context-aware systems platform.
// Copyright (c) 2006, 2007, 2008 UCD Dublin. All rights reserved.
// 
// Construct is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as
// published by the Free Software Foundation; either version 2.1 of
// the License, or (at your option) any later version.
// 
// Construct is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
// 
// You should have received a copy of the GNU Lesser General Public
// License along with Construct; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
// USA
//
// Further information about Construct can be obtained from
// http://www.construct-infrastructure.org
package org.construct_infrastructure.component.datastorage;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.io.UnsupportedEncodingException;
import java.net.URL;
import java.net.URLConnection;
import java.net.URLEncoder;
import java.sql.SQLException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.component.datastorage.observable.DataStoreObserver;
import org.construct_infrastructure.component.datastorage.observable.ObservableDataStore;
import org.construct_infrastructure.component.datastorage.observable.ObservableDataStoreImpl;
import org.construct_infrastructure.component.datastorage.viewer.DataStoreMetadataTableModelAdaptor;
import org.construct_infrastructure.component.datastorage.viewer.ViewerPanel;

import com.hp.hpl.jena.db.DBConnection;
import com.hp.hpl.jena.db.IDBConnection;
import com.hp.hpl.jena.db.ModelRDB;
import com.hp.hpl.jena.db.RDFRDBException;
import com.hp.hpl.jena.ontology.OntModel;
import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecution;
import com.hp.hpl.jena.query.QueryExecutionFactory;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.query.ResultSetFormatter;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.RDFNode;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.SimpleSelector;
import com.hp.hpl.jena.rdf.model.Statement;
import com.hp.hpl.jena.rdf.model.StmtIterator;
import com.hp.hpl.jena.reasoner.Reasoner;
import com.hp.hpl.jena.reasoner.ReasonerRegistry;
import com.hp.hpl.jena.shared.ClosedException;
import com.hp.hpl.jena.shared.JenaException;
import com.hp.hpl.jena.shared.Lock;

/**
 * The DataStoreManagerImpl is responsible for maintaining an RDF model of local and received
 * data. It also contains a meta-data model which contains information describing the RDF
 * statements stored in the first model. The implementation of this data store manager uses
 * Jena to manage the models. This class provides a single point of access to the model and
 * allows the stalling of add and remove statement requests to be performed in order to take a
 * snapshot of the current model. Periodically, expired statements (as indicated by the
 * meda-data) are removed from the data store.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public class DataStoreManagerImpl extends AbstractConstructComponent implements
      DataStoreManager {

   /**
    * The name of the main model.
    */
   private static final String MAIN_MODEL_NAME = "mainModel";

   /**
    * The name of the meta model.
    */
   private static final String META_MODEL_NAME = "metaModel";

   /**
    * The number of metadata statements per statement.
    */
   private static final int META_STATEMENT_COUNT = 1;

   /**
    * The length of time between a statement being added and expiring.
    */
   private static long my_expiryDelay;

   /**
    * The lifetime for an ontolgy.
    */
   private static final long ONTOLOGY_LIFETIME = 86400000;

   /**
    * The default value for the expiry delay if none is given (5 mins).
    */
   private static final long SYSTEM_DELAY = 300000;

   /**
    * Thirty seconds in ms.
    */
   private static final int THIRTY_SECONDS_IN_MS = 30000;

   /**
    * The panel which shows the current contents of the datastore.
    */
   private final ViewerPanel my_componentPanel;

   /**
    * The timer controlling the data ageing process.
    */
   private final DataAgeingTimer my_dataAgeingTimer;

   /**
    * The time an expiry check was last made.
    */
   private long my_lastCheckTime;

   /**
    * The model used for storing meta data.
    */
   private Model my_metaDataModel;

   /**
    * The connection to the metaModel if using a database backend.
    */
   private IDBConnection my_metaModelConnection;

   /**
    * The model used for storing data.
    */
   private Model my_model;

   /**
    * The connection to the model if using a database backend.
    */
   private IDBConnection my_modelConnection;

   /**
    * An observable object used to notify other components of changes to the data store.
    */
   private final transient ObservableDataStore my_observableDS;

   /**
    * The model used for temporarily storing data before it is added to the meta model.
    */
   private Model my_tempMetaModel;

   /**
    * The model used for temporarily storing data before it is added to the main model.
    */
   private Model my_tempModel;

   /**
    * Instantiates a new DataStoreManager which will store and provide access to RDF
    * statements.
    * 
    * @param some_properties
    *           The Properties for this component
    */
   public DataStoreManagerImpl(final Properties some_properties) {
      super();
      setProperties(some_properties);
      setExpiryTime();
      setupDataStores();
      my_observableDS = new ObservableDataStoreImpl();
      my_lastCheckTime = System.currentTimeMillis();
      loadOntologies();
      my_dataAgeingTimer = new DataAgeingTimer(this);
      my_componentPanel = new ViewerPanel(this);
      setGraphicalInterface(my_componentPanel);
   }

   /**
    * Adds an observer to the data store.
    * 
    * @param an_observer
    *           an observer to be added.
    * @throws IllegalArgumentException
    *            if the parameter an_observer is null.
    */
   public final synchronized void addObserver(final DataStoreObserver an_observer)
         throws IllegalArgumentException {
      my_observableDS.addObserver(an_observer);
   }

   /**
    * Adds a set of RDF statements to the data store with a given expiry time.
    * 
    * @param some_statements
    *           A string containing RDF to be added in N-TRIPLE format.
    * @param an_expiryTime
    *           The time when the new statements should expire.
    * @param the_origin
    *           The origin of the data.
    * @throws JenaException
    *            if badly formated RDF is passed as the some_statements parameter
    */
   public final void addStatements(final String some_statements, final long an_expiryTime,
         final Object the_origin) throws JenaException {
      if (some_statements == null) {
         throw new IllegalArgumentException("Cannot add null statements to the data store");
      }
      getModelLocks();
      // Attempt to read the N-TRIPLE data into the temporary model.
      final StringReader stringReader = new StringReader(some_statements);
      try {
         my_tempModel.read(stringReader, null, "N-TRIPLE");
         // Now we wish to construct each statement as an object and add it.
         final StmtIterator stmtIterator = my_tempModel.listStatements();
         while (stmtIterator.hasNext()) {
            final Statement statement = stmtIterator.nextStatement();
            final Resource subject = statement.getSubject();
            final Property predicate = statement.getPredicate();
            final RDFNode object = statement.getObject();
            // Construct the statement GUID.
            final String statementGUID = constructStmtGuid(subject, predicate, object);
            // Create the meta-data statement
            final Resource metaResource = my_tempMetaModel
                  .createResource(MetaData.SUBJECT_PREFIX + statementGUID);
            metaResource.addProperty(MetaData.EXPIRY_COUNTDOWN, an_expiryTime);
            final Statement[] metaData = new Statement[META_STATEMENT_COUNT];
            metaData[0] = metaResource.getProperty(MetaData.EXPIRY_COUNTDOWN);
            // Add statements
            addStatementToModel(statement);
            addStatementToMetaDataModel(metaData[0]);
            // Notify Observers
            my_observableDS.notifyObservers(ObservableDataStore.ADDED, statement, metaData,
                  the_origin);
         }
         // Close the iterator.
         stmtIterator.close();
      } catch (NullPointerException e) {
         throw new JenaException("Badly formed RDF passed to the data store");
      } finally {
         clearTempModels();
         releaseModelLocks();
      }
   }

   /**
    * Adds a set of RDF statements to the data store with the default expiry time.
    * 
    * @param some_statements
    *           RDF statements to be added in N-TRIPLE format.
    * @param the_origin
    *           The origin of the data.
    * @throws JenaException
    *            if badly formated RDF is passed as the some_statements parameter
    */
   public final void addStatements(final String some_statements, final Object the_origin)
         throws JenaException {
      addStatements(some_statements, my_expiryDelay, the_origin);
   }

   /**
    * Adds a set of RDF statements and metadata to the data store without notifying observers.
    * This method does a best-effort attempt at adding statements and meta data to the model.
    * Statements will only be added to the local model if they have at least 1 corresponsing
    * meta-statment (the expiry time). Any meta-statements that do not correspond to a
    * statement are disgarded.
    * 
    * @param some_statements
    *           RDF statements to be added in N-TRIPLE format.
    * @param some_metadata
    *           meta data associated with the statements in N-TRIPLE format.
    * @param the_origin
    *           The origin of the data.
    */
   public final void addStatementsWithMetadata(final String some_statements,
         final String some_metadata, final Object the_origin) {
      getModelLocks();
      // Read the N-TRIPLE data into the temporary models.
      try {
         final StringReader modelReader = new StringReader(some_statements);
         my_tempModel.read(modelReader, null, "N-TRIPLE");
         final StringReader metaReader = new StringReader(some_metadata);
         my_tempMetaModel.read(metaReader, null, "N-TRIPLE");
         // Construct each statement and check it has corresponding meta data.
         final StmtIterator stmtIterator = my_tempModel.listStatements();
         while (stmtIterator.hasNext()) {
            final Statement statement = stmtIterator.nextStatement();
            final Statement propertyStatement = checkModel(statement);
            if (propertyStatement != null) {
               // We can now add the statement and any corresponding
               // meta-data statements
               addStatementToModel(statement);
               final Statement[] metaData = new Statement[META_STATEMENT_COUNT];
               metaData[0] = propertyStatement;
               addStatementToMetaDataModel(propertyStatement);
               my_observableDS.notifyObservers(ObservableDataStore.ADDED, statement, metaData,
                     the_origin);
            }
         }
         // Close the iterator.
         stmtIterator.close();
      } catch (NullPointerException e) {
         throw new JenaException("Badly formed RDF passed to the data store");
      } finally {
         clearTempModels();
         releaseModelLocks();
      }
   }

   /**
    * Add a new statement to the meta-model. This is the single point from which data is added
    * to the meta-model in this class.
    * 
    * @param a_statement
    *           The statement to be added.
    */
   private void addStatementToMetaDataModel(final Statement a_statement) {
      final Resource subject = a_statement.getSubject();
      final Property predicate = a_statement.getPredicate();
      final RDFNode object = a_statement.getObject();
      // Check for an existing statement with the same
      // subject/predicate combination.
      final StmtIterator stmtIterator = my_metaDataModel.listStatements(new SimpleSelector(
            subject, predicate, (RDFNode) null));
      // If we have a result, a statement already exists with the same
      // subect and predicate. We need to delete it.
      // This situation should only arise if metadata is being added
      // independently of its
      // statement
      if (stmtIterator.hasNext()) {
         // Close the iterator.
         stmtIterator.close();
         removeStatement(a_statement);
      }
      // Finally, add the statement
      my_metaDataModel.add(subject, predicate, object);
   }

   /**
    * Add a new statement to the model. This is the single point from which data is added to
    * the model in this class.
    * 
    * @param a_statement
    *           The statement to be added.
    */
   private void addStatementToModel(final Statement a_statement) {
      final Resource subject = a_statement.getSubject();
      final Property predicate = a_statement.getPredicate();
      final RDFNode object = a_statement.getObject();
      // Check for an existing statement with the same
      // subject/predicate/object combination.
      final StmtIterator stmtIterator = my_model.listStatements(new SimpleSelector(subject,
            predicate, object));
      // If we have a result, a statement already exists with the same
      // subect and predicate. We need to delete it.
      if (stmtIterator.hasNext()) {
         // Close the iterator.
         stmtIterator.close();
         removeStatement(a_statement);
      }
      // Finally, add the statement
      my_model.add(subject, predicate, object);
   }

   /**
    * Checks to see if the temporaryMetaModel contains metadata for a given statement.
    * 
    * @param a_statement
    *           the statement about which we are looking for meta data.
    * @return the metadata Statement if true, null otherwise.
    */
   private Statement checkModel(final Statement a_statement) {
      final Resource subject = a_statement.getSubject();
      final Property predicate = a_statement.getPredicate();
      final RDFNode object = a_statement.getObject();
      // Reconstruct the statement guid from a concatenation of
      // subject, predicate and object fields.
      final String statementGUID = constructStmtGuid(subject, predicate, object);
      // Find associated expiry time meta-data statement
      final Resource metaDataResource = my_tempMetaModel.getResource(MetaData.SUBJECT_PREFIX
            + statementGUID);
      Statement propertyStatement = metaDataResource.getProperty(MetaData.EXPIRY_COUNTDOWN);
      if (propertyStatement != null) {
         // We have an expiry time. The final check is that it is greater than 0
         try {
            final long expiryTime = Long.valueOf(propertyStatement.getObject().toString())
                  .longValue();
            if (!(expiryTime > 0)) {
               propertyStatement = null;
            }
         } catch (NumberFormatException e) {
            getLogger().warning(
                  "Statement with invalid expiry time "
                        + "arriving from the gossiping layer: " + e.getMessage());
         }
      }
      return propertyStatement;
   }

   /**
    * Clears the temporary models.
    */
   private void clearTempModels() {
      my_tempModel.removeAll();
      my_tempMetaModel.removeAll();
   }

   /**
    * Connects the jena models to a database.
    * 
    * @param a_driverName
    *           the name of the database driver.
    * @param a_url
    *           the url for the database.
    * @param a_user
    *           the username required to access the database.
    * @param a_password
    *           the password required to access the database
    * @param a_type
    *           the type of the database
    * @return true if the connection was made, false otherwise
    */
   private boolean connectToDatabase(final String a_driverName, final String a_url,
         final String a_user, final String a_password, final String a_type) {
      boolean success = false;
      try {
         Class.forName(a_driverName);
         getLogger().info("Connecting to database of type: " + a_type);
         my_modelConnection = new DBConnection(a_url, a_user, a_password, a_type);
         my_metaModelConnection = new DBConnection(a_url, a_user, a_password, a_type);
         // If there is an existing model, we wish to delete it.
         if (my_modelConnection.containsModel(MAIN_MODEL_NAME)) {
            final ModelRDB tempModel = ModelRDB.open(my_modelConnection, MAIN_MODEL_NAME);
            tempModel.remove();
            tempModel.close();
         }
         // Create the model
         my_model = ModelRDB.createModel(my_modelConnection, MAIN_MODEL_NAME);
         // If there is an existing model, we wish to delete it.
         if (my_metaModelConnection.containsModel(META_MODEL_NAME)) {
            final ModelRDB tempModel = ModelRDB.open(my_metaModelConnection, META_MODEL_NAME);
            tempModel.remove();
            tempModel.close();
         }
         // Create the meta model
         my_metaDataModel = ModelRDB.createModel(my_metaModelConnection, META_MODEL_NAME);
         success = true;
      } catch (ClassNotFoundException e) {
         getLogger().warning("Cound not load database driver: " + a_driverName);
      } catch (RDFRDBException e) {
         getLogger().warning("Another process is currently using the database");
         try {
            my_modelConnection.close();
            my_metaModelConnection.close();
         } catch (SQLException ex) {
            getLogger().warning("Could not close connections to database: " + ex.getMessage());
         }
      }
      return success;
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
         getLogger().warning(an_exception.getMessage());
      }
      return result;
   }

   /**
    * Deletes an observer from the data store.
    * 
    * @param an_observer
    *           the observer to be deleted.
    */
   public final synchronized void deleteObserver(final DataStoreObserver an_observer) {
      my_observableDS.deleteObserver(an_observer);
   }

   /**
    * Gets the locks on all the models.
    */
   private void getModelLocks() {
      // Get a lock on the models
      my_model.enterCriticalSection(Lock.WRITE);
      my_metaDataModel.enterCriticalSection(Lock.WRITE);
      my_tempModel.enterCriticalSection(Lock.WRITE);
      my_tempMetaModel.enterCriticalSection(Lock.WRITE);
   }

   /**
    * Get the expiry timer for the given statement.
    * 
    * @param a_statement
    *           The statement in N-TRIPLE format.
    * @return The current expiry timer count for the given statement or -1 if the statement
    *         does not exist.
    */
   public final long getStatementExpiryTimer(final String a_statement) {
      long expiryTimer = -1;
      my_metaDataModel.enterCriticalSection(Lock.READ);

      try {
         // use Jena to read the statement
         final Model model = ModelFactory.createDefaultModel();
         model.read(new ByteArrayInputStream(a_statement.getBytes()), null, "N-TRIPLE");

         // ensure we have at least one statement
         if (!model.isEmpty()) {
            // get it and generate its GUID
            final Statement statement = model.listStatements().nextStatement();
            final String statementGUID = constructStmtGuid(statement.getSubject(), statement
                  .getPredicate(), statement.getObject());

            // find its metadata
            final Resource metaDataResource = my_metaDataModel
                  .getResource("http://system.metadata/" + statementGUID);
            final Statement propertyStatement = metaDataResource
                  .getProperty(MetaData.EXPIRY_COUNTDOWN);

            // if the expiry timer exists, convert it to a long for return
            if (propertyStatement != null) {
               final String expiryTimerString = propertyStatement.getObject().toString();
               expiryTimer = Long.parseLong(expiryTimerString);
            }
         }
      } finally {
         my_metaDataModel.leaveCriticalSection();
      }
      return expiryTimer;
   }

   /**
    * This method checks the meta data belonging to a statement to see if a statement has
    * expired. It also updates the expiry countdown timer in the system metadata.
    * 
    * @param a_statement
    *           The statement we wish to check for expiration.
    * @param the_timeElapsed
    *           The time that has elapsed since the last check
    * @return true if the statement has expired, false otherwise.
    */
   public final boolean hasStatementExpired(final Statement a_statement,
         final long the_timeElapsed) {
      boolean result = false;
      final Resource subject = a_statement.getSubject();
      final Property predicate = a_statement.getPredicate();
      final RDFNode object = a_statement.getObject();
      // Reconstruct the statement guid from a concatenation of
      // subject, predicate and object fields.
      final String statementGUID = constructStmtGuid(subject, predicate, object);
      // Find associated meta-data statement
      final Resource metaDataResource = my_metaDataModel.getResource(MetaData.SUBJECT_PREFIX
            + statementGUID);
      final Statement propertyStatement = metaDataResource
            .getProperty(MetaData.EXPIRY_COUNTDOWN);
      final String expiryTimerString = propertyStatement.getObject().toString();
      long expiryTimer = Long.parseLong(expiryTimerString);
      // Update the expiry time
      expiryTimer -= the_timeElapsed;
      // Update the statement
      propertyStatement.changeObject(expiryTimer);
      if (expiryTimer <= 0) {
         result = true;
      }
      return result;
   }

   /**
    * Loads the ontologies into the datastore.
    */
   private void loadOntologies() {
      // Iterate through all the datastore properties
      final Iterator entries = getProperties().entrySet().iterator();
      // add all ontologies
      while (entries.hasNext()) {
         final Map.Entry entry = (Map.Entry) entries.next();
         final String type = (String) entry.getKey();
         // Check if it is an ontology
         if (type.startsWith("o:")) {
            try {
               // get the uri and construct the model
               final String address = (String) entry.getValue();
               final Model model = readFromURL(address);
               final ByteArrayOutputStream byteOutStream = new ByteArrayOutputStream();
               model.write(byteOutStream, "N-TRIPLE");
               addStatements(byteOutStream.toString().replace('\n', ' '), ONTOLOGY_LIFETIME,
                     "ONTOLOGY_LOADER");
            } catch (JenaException e) {
               getLogger().warning("Could not load ontology from: " + entry.getValue());
            }
         }
      }
   }

   /**
    * Schedules the task for maintaining the model.
    */
   public final void onRun() {
      my_dataAgeingTimer.scheduleUpdates();
      my_componentPanel.setTableModel(new DataStoreMetadataTableModelAdaptor(this, my_model,
            my_metaDataModel));
   }

   /**
    * Closes the model before shutting down.
    */
   public final void onShutdown() {
      try {
         my_dataAgeingTimer.cancel();
         getModelLocks();
         // Close connections. This is done differently depending on whether or not we have an
         // in memory store.
         if (my_modelConnection == null) {
            my_model.close();
         } else {
            try {
               my_modelConnection.close();
            } catch (SQLException e) {
               getLogger().warning(
                     "Error when closing database connection to model: " + e.getMessage());
            }
         }
         if (my_metaModelConnection == null) {
            my_metaDataModel.close();
         } else {
            try {
               my_metaModelConnection.close();
            } catch (SQLException e) {
               getLogger().warning(
                     "Error when closing database connection to metaModel: " + e.getMessage());
            }
         }
      } finally {
         releaseModelLocks();
      }
   }

   /**
    * This method reads an ontology from a URL.
    * 
    * @return OntModel
    * @param a_url
    *           the URL of the ontology to be read
    */
   private OntModel readFromURL(final String a_url) {
      final OntModel modelFromURL = ModelFactory.createOntologyModel();
      try {
         final URL ont_url = new URL(a_url);
         // create the connection the the remote file
         final URLConnection conn = ont_url.openConnection();
         // set the timeout for the connection to 30 seconds
         conn.setConnectTimeout(THIRTY_SECONDS_IN_MS);
         // make a connection
         conn.connect();
         final BufferedReader reader = new BufferedReader(new InputStreamReader(conn
               .getInputStream()));
         modelFromURL.read(reader, null);
         reader.close();
      } catch (FileNotFoundException e) {
         getLogger().severe("File not found error: " + e.getMessage() + " :" + a_url);
      } catch (IOException e) {
         getLogger().severe("IO error: " + e.getMessage());
      }
      return modelFromURL;
   }

   /**
    * Releases the locks on all the models.
    */
   private void releaseModelLocks() {
      my_tempMetaModel.leaveCriticalSection();
      my_tempModel.leaveCriticalSection();
      my_metaDataModel.leaveCriticalSection();
      my_model.leaveCriticalSection();
   }

   /**
    * This method iterates through all the statements in the data store and checks the
    * associated expiry date as given in the metadata. If the expiry data < now the statement
    * (and its metadata is deleted).
    */
   public final void removeAllExpiredStatements() {
      // Create a timestamp for the current time.
      final long currentTime = System.currentTimeMillis();
      // Work out time elased since last check
      final long timeElapsedSinceLastCheck = currentTime - my_lastCheckTime;
      // Update last check time
      my_lastCheckTime = currentTime;
      // Create a list to contain the statements to be deleted.
      final List stmtsToBeDeleted = new LinkedList();
      // Get lock on model
      getModelLocks();
      try {
         final StmtIterator stmtIterator = my_model.listStatements();
         while (stmtIterator.hasNext()) {
            final Statement statement = stmtIterator.nextStatement();
            if (hasStatementExpired(statement, timeElapsedSinceLastCheck)) {
               stmtsToBeDeleted.add(statement);
            }
         }
         // Close the iterator
         stmtIterator.close();
         // We now have a list of all expired statements. Now we delete them
         final Iterator statementIterator = stmtsToBeDeleted.iterator();
         while (statementIterator.hasNext()) {
            removeStatement((Statement) statementIterator.next());
         }
      } catch (ClosedException e) {
         getLogger().warning("Attempting delete on closed model");
      } finally {
         // Release lock on model
         releaseModelLocks();
      }
   }

   /**
    * Removes a single statement and associated meta-data from the model. Note that the calling
    * method MUST have the write lock on both the model and the metadata model before calling
    * this method.
    * 
    * @param a_statement
    *           The statement to be deleted.
    */
   private void removeStatement(final Statement a_statement) {
      final Resource subject = a_statement.getSubject();
      final Property predicate = a_statement.getPredicate();
      final RDFNode object = a_statement.getObject();
      // Reconstruct the statement guid
      final String statementGUID = constructStmtGuid(subject, predicate, object);
      // Find associated meta-data statement
      final Resource metaDataResource = my_metaDataModel.getResource(MetaData.SUBJECT_PREFIX
            + statementGUID);

      // Notify observers of the removal
      my_observableDS.notifyObservers(ObservableDataStore.REMOVED, a_statement, null, null);

      // Remove the expired statement from the model.
      my_model.remove(a_statement);
      // Remove all the meta-data statements corresponding to the deleted
      // statement
      my_metaDataModel.remove(my_metaDataModel.listStatements(new SimpleSelector(
            metaDataResource, null, (RDFNode) null)));
   }

   /**
    * Runs a query on the Datastore. The query can be in either SPARQL or RDQL form. The model
    * must first be reasoned about so that inferred triples will be included.
    * 
    * @param a_query
    *           the query to be run
    * @return the results of the query
    */
   public final String runQuery(final String a_query) {
      String result = "";
      // System.err.println(a_query);
      getModelLocks();
      try {
         final Query query = QueryFactory.create(a_query);
         // create the inferred model
         final Reasoner owlReasoner = ReasonerRegistry.getOWLReasoner();
         owlReasoner.bindSchema(my_model);
         // final InfModel infModel = ModelFactory.createInfModel(owlReasoner, my_model);
         // TODO KNOX ADRIAN - An issue arrises when using the inferenced model. Queries have
         // been changed to work with the normal model for the moment.
         final QueryExecution qexec = QueryExecutionFactory.create(query, my_model);
         final ResultSet resultSet = qexec.execSelect();
         final ByteArrayOutputStream byteOutStream = new ByteArrayOutputStream();
         ResultSetFormatter.outputAsRDF(byteOutStream, "N-TRIPLE", resultSet);

         result = byteOutStream.toString();
         // Remove newlines
         result = result.replace('\n', ' ');
      } finally {
         releaseModelLocks();
      }
      return result;
   }

   /**
    * Checks to see if the user has specified an expiry time. If not, the default time is used.
    */
   private void setExpiryTime() {
      // Set the default expiry time
      final String expiryTime = getProperties().getProperty("expiryTime");
      if (expiryTime == null) {
         my_expiryDelay = SYSTEM_DELAY;
      } else {
         try {
            my_expiryDelay = new Long(expiryTime).longValue();
         } catch (NumberFormatException e) {
            getLogger().warning(
                  "The specified default expiry time (" + expiryTime + ") is not valid");
            my_expiryDelay = SYSTEM_DELAY;
         }
      }
   }

   /**
    * Implementation of setupComponentLinks() method (not used).
    */
   public void setupComponentLinks() {
      // Method not used
   }

   /**
    * Sets up the main databases based on settings on the properies files. We will check for
    * the required properties in the database. If not all exist, we run off an in memory data
    * store.
    */
   private void setupDataStores() {
      // Get properties
      my_modelConnection = null;
      my_metaModelConnection = null;
      my_tempModel = ModelFactory.createDefaultModel();
      my_tempMetaModel = ModelFactory.createDefaultModel();
      final String driverName = getProperties().getProperty("d:driver");
      final String url = getProperties().getProperty("d:url");
      final String user = getProperties().getProperty("d:user");
      final String password = getProperties().getProperty("d:password");
      final String type = getProperties().getProperty("d:dbtype");
      // If all properties exist attempt to set up the database connections.
      boolean useInMemory = true;
      if (driverName != null && url != null && user != null && password != null
            && type != null) {
         useInMemory ^= connectToDatabase(driverName, url, user, password, type);
      }
      if (useInMemory) {
         // Run off an internal store.
         getLogger().info("Using an in memory data store");
         my_model = ModelFactory.createDefaultModel();
         my_metaDataModel = ModelFactory.createDefaultModel();
      }
   }
}
