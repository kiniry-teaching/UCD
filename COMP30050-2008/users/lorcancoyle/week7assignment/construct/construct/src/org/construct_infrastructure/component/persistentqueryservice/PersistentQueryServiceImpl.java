//
// $Revision: 7373 $: $Date: 2008-01-24 11:20:18 +0000 (Thu, 24 Jan 2008) $ - $Author:
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
package org.construct_infrastructure.component.persistentqueryservice;


import java.io.IOException;
import java.io.PrintStream;
import java.util.Collection;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.logging.Logger;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.component.discovery.RegistryService;
import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.io.ServiceComponentDescriptor;
import org.construct_infrastructure.loader.ConstructProperties;

/**
 * This class defines the operations which a persistent query service should implement. A
 * persistent query service is a query service which accepts queries and executes them
 * asynchonously and continuously every minute. The queries are executed in a round-robin
 * fashion and may be cancelled at any time.
 * 
 * @author Adrian Clear (adrian.clear@ucd.ie)
 */
public class PersistentQueryServiceImpl extends AbstractConstructComponent implements
      PersistentQueryService {

   /**
    * The interface to the registry service.
    */
   public static final String RSERVICE_MANAGER = "org.construct_infrastructure.component.discovery.RegistryService";

   /**
    * This is used for logging in this Class.
    */
   private static final Logger LOGGER = Logger.getLogger(PersistentQueryServiceImpl.class
         .getName());

   /**
    * The registry service that holds a reference to the registry service.
    */
   private transient RegistryService my_registryService;

   /**
    * The interval between each execution of queries.
    */
   private int my_interval_seconds;

   /**
    * The socket that listens for new data submissions.
    */
   private PersistentQueryServiceSocket my_socket;

   /**
    * The number of threads to maintain.
    */
   private int my_pool_size;

   /**
    * A map which contains the queries.
    */
   private final Map my_query_table;

   /**
    * An executer service used to query every 60 seconds.
    */
   private final ScheduledExecutorService my_service_scheduler;

   /**
    * An executer service used to run through the queries in round-robin fashion.
    */
   private final ExecutorService my_query_scheduler;

   /**
    * A runnable object that executes each query once in round-robin fashion.
    */
   private final Runnable my_queryer = new Runnable() {
      public void run() {
         if (!my_query_table.isEmpty()) {
            final Collection c = my_query_table.values();
            final Iterator i = c.iterator();
            while (i.hasNext()) {
               my_query_scheduler.execute((Runnable) i.next());
            }
         }
      }
   };

   /**
    * The constructor for this class.
    * 
    * @param some_properties
    *           the properties of this class.
    */
   public PersistentQueryServiceImpl(final Properties some_properties) {
      super();
      setProperties(some_properties);
      final String portProperty = (String) getProperties().get("port");
      my_pool_size = Integer.parseInt((String) getProperties().get("pool"));
      my_interval_seconds = Integer.parseInt((String) getProperties().get("interval"));
      int port = 0;
      try {
         if (portProperty != null) {
            port = Integer.parseInt(portProperty);
         }
      } catch (NumberFormatException e) {
         LOGGER.warning("Invalid port number specified"
               + " in properties. Using next available port");
      }
      try {
         my_socket = new PersistentQueryServiceSocket(LOGGER, port);
         new Thread(my_socket).start();
      } catch (IOException e) {
         LOGGER.severe("Could not open socket to listen for client requests");
      }

      my_service_scheduler = Executors.newScheduledThreadPool(my_pool_size);
      my_query_scheduler = Executors.newSingleThreadExecutor();
      my_query_table = new Hashtable();
      my_service_scheduler.scheduleAtFixedRate(my_queryer, 0, my_interval_seconds,
            java.util.concurrent.TimeUnit.SECONDS);
   }

   /**
    * This method starts the timed task which calls the maintainEntityDirectory() method.
    */
   public final void onRun() {
      final String name = PQS_NAME;
      final String description = "The persistent query service: Connect via a "
            + "socket and send SPARQL queries. Response strings will be SPARQL result sets in RDF"
            + " and will be delivered asynchronously until the query is cancelled";
      final Object hostNameProperty = ConstructProperties.getHostName();
      if (hostNameProperty != null) {
         final String host = (String) hostNameProperty;
         final int port = my_socket.getLocalPort();
         final String misc = "See example applications.";

         final ServiceComponentDescriptor dataportDescriptor = new ServiceComponentDescriptor(
               name, description, host, port, misc);
         my_registryService.registerService(dataportDescriptor);
      } else {
         LOGGER.info("Not registering with registry service - no hostname property");
      }
   }

   /**
    * This method is called when the component is shutdown.
    */
   public final void onShutdown() {
      if (my_socket != null) {
         my_socket.shutdown();
      }
      if (my_service_scheduler != null) {
         my_service_scheduler.shutdownNow();
      }

   }

   /**
    * This method is a placeholder. It is called after construction, but before the run method
    * is called. Subclasses should use this method to gain references they require from the
    * component registry.
    * 
    * @throws NoSuchComponentException
    *            if an attempt is made to access a component which doesnt exist.
    */
   public final void setupComponentLinks() throws NoSuchComponentException {
      my_registryService = (RegistryService) ComponentRegistry.getComponent(RSERVICE_MANAGER);
   }

   /**
    * Adds a query for asynchronous execution.
    * 
    * @param the_query
    *           the query string
    * @param the_queryID
    *           the unique id for the query
    * @param the_outputStream
    *           the output stream for callbacks
    */
   public final void query(final String the_query, final String the_queryID,
         final PrintStream the_outputStream) {
      my_query_table.put(Integer.valueOf(the_queryID.hashCode()), new PersistentQuery(
            the_query, the_queryID, the_outputStream));
   }

   /**
    * Remove a query from asynchronous execution.
    * 
    * @param the_queryID
    *           the unique id of the query
    */
   public final void cancelQuery(final String the_queryID) {
      my_query_table.remove(Integer.valueOf(the_queryID.hashCode()));
   }

}
