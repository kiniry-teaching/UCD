//
// $Revision: 7904 $: $Date: 2008-02-26 16:41:59 +0000 (Tue, 26 Feb 2008) $ - $Author:
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
package org.construct_infrastructure.component.queryservice;


import java.io.IOException;
import java.util.Properties;
import java.util.logging.Logger;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.component.datastorage.DataStoreManager;
import org.construct_infrastructure.component.discovery.RegistryService;
import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.io.ServiceComponentDescriptor;
import org.construct_infrastructure.loader.ConstructProperties;

import com.hp.hpl.jena.query.QueryException;

/**
 * The query service is responsible for processing application and entity queries made in
 * sparql.
 * 
 * @author stephen.knox@ucd.ie
 * @author adrian.clear@ucd.ie
 */
public class QueryServiceImpl extends AbstractConstructComponent implements QueryService {
   /**
    * The interface for the data store manager.
    */
   public static final String DSTORE_MANAGER = "org.construct_infrastructure.component.datastorage.DataStoreManager";

   /**
    * The interface to the registry service.
    */
   public static final String RSERVICE_MANAGER = "org.construct_infrastructure.component.discovery.RegistryService";

   /**
    * This is used for logging in this Class.
    */
   private static final Logger LOGGER = Logger.getLogger(QueryServiceImpl.class.getName());

   /**
    * The datastore manager that holds all the data that is queryable from this. QueryService
    */
   private transient DataStoreManager my_dataStoreManager;

   /**
    * The registry service that holds a reference to the registry service.
    */
   private transient RegistryService my_registryService;

   /**
    * The socket that listens for new data submissions.
    */
   private QueryServiceSocket my_socket;

   public QueryServiceImpl(Properties some_properties) {
      super();
      setProperties(some_properties);
      String portProperty = (String) getProperties().get("port");
      int port = 0; // if we send port 0 to the data port socket it will bind to next
      // available port
      try {
         if (portProperty != null) {
            port = Integer.parseInt(portProperty);
         }
      } catch (NumberFormatException e) {
         getLogger().warning(
               "Invalid port number specified in properties. Using next available port");
      }
      // Start up the socket to listen for client requests
      try {
         my_socket = new QueryServiceSocket(getLogger(), port);
         new Thread(my_socket).start();
      } catch (IOException e) {
         getLogger().severe("Could not open socket to listen for client requests");
      }
   }

   /**
    * This method starts the timed task which calls the maintainEntityDirectory() method. <JML>
    * also ensures dataStoreManager != null; </JML>
    */
   public void onRun() {
      String name = QS_NAME;
      String description = "The query service: Connect via a socket and send SPARQL queries. Response string will be a SPARQL result set in RDF.";
      Object hostNameProperty = ConstructProperties.getHostName();
      if (hostNameProperty != null) {
         String host = (String) hostNameProperty;
         int port = my_socket.getLocalPort();
         String misc = "See example applications.";

         ServiceComponentDescriptor dataportDescriptor = new ServiceComponentDescriptor(name,
               description, host, port, misc);
         my_registryService.registerService(dataportDescriptor);
      } else {
         getLogger().info("Not registering with registry service - no hostname property");
      }
   }

   public void onShutdown() {
      if (my_socket != null) {
         my_socket.shutdown();
      }
   }

   /**
    * This method is a place-holder. It is called after construction, but before the run method
    * is called. Subclasses should use this method to gain references they require from the
    * component registry.
    * 
    * @throws NoSuchComponentException
    *            if an attempt is made to access a component which does not exist.
    */
   public final void setupComponentLinks() throws NoSuchComponentException {
      my_dataStoreManager = (DataStoreManager) ComponentRegistry.getComponent(DSTORE_MANAGER);
      my_registryService = (RegistryService) ComponentRegistry.getComponent(RSERVICE_MANAGER);
   }

   /**
    * This method processes and immediately evaluates a query.
    * 
    * @param the_query
    *           the query to be evaluated
    * @return the set of results that satisfy the query or null if an error occured processing
    *         the query.
    */

   public final String synchronousQuery(final String the_query) {
      String result = null;
      try {
         result = my_dataStoreManager.runQuery(the_query);
      } catch (QueryException e) {
         LOGGER.severe(e.getMessage());
      }
      return result;
   }
}
