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
package org.construct_infrastructure.component.dataport;


import java.io.IOException;
import java.util.Properties;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.component.datastorage.DataStoreManager;
import org.construct_infrastructure.component.discovery.RegistryService;
import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.io.ServiceComponentDescriptor;
import org.construct_infrastructure.io.ServiceSocket;
import org.construct_infrastructure.loader.ConstructProperties;

import com.hp.hpl.jena.shared.JenaException;

/**
 * The data port accepts RDF data provided by sensors and adds it to the data store.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class DataPortImpl extends AbstractConstructComponent implements DataPort {

   /**
    * The interface for the data store manager.
    */
   public static final String DSTORE_MANAGER = "org.construct_infrastructure.component"
         + ".datastorage.DataStoreManager";

   /**
    * The interface to the registry service.
    */
   public static final String RSERVICE_MANAGER = "org.construct_infrastructure.component"
         + ".discovery.RegistryService";

   /**
    * The datastore manager that holds a reference to the data store.
    */
   private transient DataStoreManager my_dataStoreManager;

   /**
    * The registry service that holds a reference to the registry service.
    */
   private transient RegistryService my_registryService;

   /**
    * The socket that listens for new data submissions.
    */
   private ServiceSocket my_socket;

   /**
    * Creates a new Data Port.
    * 
    * @param some_properties
    *           the properties for this component.
    */
   public DataPortImpl(final Properties some_properties) {
      super();
      setProperties(some_properties);
      startServer();
   }

   /**
    * Start the server listening.
    */
   private void startServer() {
      final String portProperty = (String) getProperties().get("port");
      int port = 0; // if we send port 0 to the data port socket it will bind to next
      // available port
      try {
         if (portProperty != null) {
            port = Integer.parseInt(portProperty);
         }
         my_socket = new DataPortSocket(getLogger(), port);
         new Thread(my_socket).start();
      } catch (NumberFormatException e) {
         getLogger().warning(
               "Invalid port number specified in properties. Using next available port");
      } catch (IOException e) {
         getLogger().severe("Could not open socket to listen for client requests");
      }
   }

   /**
    * Replace multiple whitespaces between words with single blank space.
    * 
    * @param a_string
    *           The string to perform the replace on
    * @return the modified string
    */
   private static String itrim(final String a_string) {
      return a_string.replaceAll("\\b\\s{2,}\\b", " ");
   }

   /**
    * Removes leading whitespace from a string.
    * 
    * @param a_string
    *           The string to perform the replace on
    * @return the modified string
    */
   private static String ltrim(final String a_string) {
      return a_string.replaceAll("^\\s+", "");
   }

   /**
    * Remove trailing whitespace from a string.
    * 
    * @param a_string
    *           The string to perform the replace on
    * @return the modified string
    */
   private static String rtrim(final String a_string) {
      return a_string.replaceAll("\\s+$", "");
   }

   /**
    * Removes all superfluous whitespaces in source string.
    * 
    * @param a_string
    *           The string to perform the replace on
    * @return the modified string
    */
   private static String trim(final String a_string) {
      return itrim(ltrim(rtrim(a_string)));
   }

   /**
    * Takes in a set of RDF statements in N-TRIPLE format to add to the data model. The form
    * N-TRIPLE (SPO.) + time-to-live (long) should be used where an explicit time-to-live value
    * is associated with the statements being passed in. The time should only be specified
    * after the last statement in the String, and will apply to all statements.
    * 
    * @param some_data
    *           a string containing data to be added to the data store with an optional
    *           timestamp.
    * @return true if the data was added successfully, false otherwise.
    */
   public boolean addData(final String some_data) {
      boolean rtnValue = true;
      if (some_data == null) {
         rtnValue = false;
      } else {
         // Remove whitespace
         final String trimmed_data = DataPortImpl.trim(some_data);
         // Check if we have a timestamp and take the appropriate action.
         if (trimmed_data.endsWith(".")) {
            try {
               addStmtWithoutExpiry(trimmed_data);
            } catch (JenaException e) {
               getLogger().info("Failed to add data to the model: " + e.getMessage());
               rtnValue = false;
            }
         } else {
            try {
               addStmtWithExpiry(trimmed_data.substring(0, trimmed_data.lastIndexOf('.') + 1),
                     trimmed_data.substring(trimmed_data.lastIndexOf('.') + 1, trimmed_data
                           .length()));
            } catch (JenaException e) {
               getLogger().info("Failed to add data to the model: " + e.getMessage());
               rtnValue = false;
            } catch (NumberFormatException e) {
               getLogger().info(
                     "Failed to add data to the model, invalid timestamp: " + e.getMessage());
               rtnValue = false;
            }
         }
      }
      return rtnValue;
   }

   /**
    * This method adds a new statement (without an expiry tiime) to the data_store.
    * 
    * @param a_statement
    *           the statement to be added in N-TRIPLE format.
    */
   private void addStmtWithoutExpiry(final String a_statement) {
      // Add the statement to the data store
      my_dataStoreManager.addStatements(a_statement, "DATA_PORT");
   }

   /**
    * This method adds a new statement to the data_store with a given timestamp.
    * 
    * @param a_statement
    *           the statement to be added in N-TRIPLE format.
    * @param an_expiryTime
    *           the expiry time for the statement expresed as a long.
    */
   private void addStmtWithExpiry(final String a_statement, final String an_expiryTime) {
      // Add statement to the data store
      final long expiryTime = Long.parseLong(DataPortImpl.trim(an_expiryTime));
      my_dataStoreManager.addStatements(a_statement, expiryTime, "DATA_PORT");
   }

   /**
    * Cancel the cycle timer before shutting down.
    */
   public void onShutdown() {
      if (my_socket != null) {
         my_socket.shutdown();
      }
   }

   /**
    * Used by the data port to gain a reference to the data store and the registry service.
    * 
    * @throws NoSuchComponentException
    *            if an attempt is made to access a component which doesnt exist.
    */
   public void setupComponentLinks() throws NoSuchComponentException {
      my_dataStoreManager = (DataStoreManager) ComponentRegistry.getComponent(DSTORE_MANAGER);
      my_registryService = (RegistryService) ComponentRegistry.getComponent(RSERVICE_MANAGER);
   }

   /**
    * Gets the org.construct_infrastructure.component.discovery.RegistryService and registers the data
    * port for discovery and use by the outside world.
    */
   public void onRun() {
      final String description = "Raw data port: Connect via a socket and send "
            + "N-TRIPLE RDF strings. Response string will be ok or error if it fails.";
      final Object hostNameProperty = ConstructProperties.getHostName();
      if (hostNameProperty == null) {
         getLogger().info("Not registering with registry service - no hostname property");
      } else {
         final String host = (String) hostNameProperty;
         final int port = my_socket.getLocalPort();
         final String misc = "See example applications.";
         final ServiceComponentDescriptor dataportDescriptor = new ServiceComponentDescriptor(
               DP_NAME, description, host, port, misc);
         my_registryService.registerService(dataportDescriptor);
      }
   }

}
