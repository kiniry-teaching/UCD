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
package org.construct_infrastructure.loader;


import java.io.File;
import java.io.IOException;
import java.util.Calendar;
import java.util.GregorianCalendar;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

import javax.swing.JPanel;

import org.construct_infrastructure.component.ComponentRuntimeException;
import org.construct_infrastructure.component.ConstructComponent;
import org.construct_infrastructure.componentregistry.ComponentInstantiationException;
import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.ComponentRegistryException;
import org.construct_infrastructure.componentregistry.InvalidComponentException;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.gui.ConstructGUI;

/**
 * The Construct class is responsible for launching all the components of the local framework.
 * The details outlining which implementation to instantiate for each component is specified in
 * a property file. Each component is then constructed using reflection.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class ComponentLoader {

   /**
    * A constant representing the number 10.
    */
   private static final int TEN = 10;

   /**
    * The logger which handles messsages to be logged.
    */
   private static final Logger LOGGER = Logger.getLogger("org.construct_infrastructure");

   /**
    * The Construct properties (loaded from file in the constructor).
    */
   private final ConstructProperties my_properties;

   /**
    * The Construct GUI.
    */
   private final transient ConstructGUI my_gui;

   /**
    * Contains all the running components.
    */
   private final Map my_activeComponents;

   /**
    * The executor that creates threads to run the components.
    */
   private final ExecutorService my_executorService;

   /**
    * Creates a new Construct object with output directed to a gui. This involves checking the
    * presence of core properties in the properties file, and starting up all specified
    * components.
    * 
    * @param a_gui
    *           The context server GUI
    * @param the_propertiesFile
    *           the ConStruct properties file
    * @throws PropertyFileException
    *            if the Context Server fails to initialise due to a problem with the property
    *            file.
    * @throws ComponentCreationException
    *            if the Context Server fails to initialise due to an inability to initialise a
    *            component.
    */
   public ComponentLoader(final ConstructGUI a_gui, final File the_propertiesFile)
         throws PropertyFileException, ComponentCreationException {
      super();
      my_gui = a_gui;
      // load property file
      my_properties = new ConstructProperties();
      my_properties.loadConstructProperties(the_propertiesFile);
      // Initialise the component Set
      my_activeComponents = new Hashtable();
      setupLoggerConfiguration();
      checkHostName();
      // The executor that creates threads to run the components.
      my_executorService = Executors.newCachedThreadPool();
      // Start all the components
      try {
         startupAllComponents();
      } catch (ComponentRegistryException e) {
         LOGGER.severe("Failed while initialising components: " + e.getMessage());
         throw new ComponentCreationException(e.getMessage(), e.fillInStackTrace());
      }
   }

   public void checkHostName() {
      String hostName = ConstructProperties.getHostName();
      if (hostName == null || hostName.equalsIgnoreCase("SET-ME")) {
         LOGGER.warning("No hostname property found. Attempting to auto detect hostname...");
         ConstructProperties.autoDetectHostName();
         hostName = ConstructProperties.getHostName();
         LOGGER.warning("hostname set to: " + hostName);
      }

      if (hostName.equals("127.0.0.1") || hostName.equalsIgnoreCase("localhost")) {
         LOGGER.severe("Hostname is set to " + hostName
               + ". This is probably an error. Please check your construct.properties file and set the correct value.");
      }
   }

   /**
    * Creates a new Construct object with output directed to the console. This involves
    * checking the presence of core properties in the properties file, and starting up all
    * specified components.
    * 
    * @param the_propertiesFile
    *           the ConStruct properties file
    * @throws PropertyFileException
    *            if the Context Server fails to initialise due to a problem with the property
    *            file.
    * @throws ComponentCreationException
    *            if the Context Server fails to initialise due to an inability to initialise a
    *            component.
    */
   public ComponentLoader(final File the_propertiesFile) throws PropertyFileException,
         ComponentCreationException {
      super();
      my_gui = null;
      // load property file
      my_properties = new ConstructProperties();
      my_properties.loadConstructProperties(the_propertiesFile);
      // Initialise the component Set
      my_activeComponents = new Hashtable();
      setupLoggerConfiguration();
      checkHostName();
      // The executor that creates threads to run the components.
      my_executorService = Executors.newCachedThreadPool();
      // Start all the components
      try {
         startupAllComponents();
      } catch (ComponentRegistryException e) {
         LOGGER.severe("Failed while initialising components: " + e.getMessage());
         throw new ComponentCreationException(e.getMessage(), e.fillInStackTrace());
      }
   }

   /**
    * Removes the root logger and redirects output to the GUI.
    * 
    * @throws PropertyFileException
    *            if the logging level has not been set in the properties.
    */
   private void setupLoggerConfiguration() throws PropertyFileException {
      // Close and remove existing logging handlers if there is a GUI
      if (my_gui != null) {
         final Handler[] handlers = LOGGER.getParent().getHandlers();
         for (int i = 0; i < handlers.length; i++) {
            final Handler handler = handlers[i];
            handler.close();
            LOGGER.getParent().removeHandler(handler);
         }
         // Add a gui handler to the logger
         LOGGER.getParent().addHandler(new StringHandler(my_gui));
      }
      // Set the logging level
      try {
         final String loggingLevel = (String) my_properties.get("loggingLevel");
         if (loggingLevel == null) {
            throw new IllegalArgumentException("Logging Level is null");
         } else {
            LOGGER.setLevel(Level.parse(loggingLevel));
         }
      } catch (IllegalArgumentException e) {
         throw new PropertyFileException("The logging level is not specified correctly: "
               + e.getMessage(), e.fillInStackTrace());
      }
      // Add a file handler to the logger
      try {
         Calendar now = new GregorianCalendar();
         now.setTimeInMillis(System.currentTimeMillis());
         final Handler fileHandler = new FileHandler((String) my_properties
               .get("logDirectory")
               + now.get(Calendar.DAY_OF_MONTH)
               + "-"
               + now.get(Calendar.MONTH)
               + "-"
               + now.get(Calendar.YEAR)
               + "@"
               + now.get(Calendar.HOUR_OF_DAY)
               + "-"
               + now.get(Calendar.MINUTE) + "-" + (String) my_properties.get("logFileName"),
               Integer.parseInt((String) my_properties.get("loggingLimit")), Integer
                     .parseInt((String) my_properties.get("loggingFileCount")), false);
         LOGGER.addHandler(fileHandler);
      } catch (IOException e) {
         LOGGER.warning("Unable to add a file handler to the logger: " + e.getMessage());
      }

   }

   /**
    * Called automatically when the server is to be shutdown. This method shuts down each of
    * the components that are registered in the component registry. The order in which the
    * components are shutdown is not ensured.
    */
   public void shutdown() {
      // Set the executor to shutdown
      my_executorService.shutdown();
      // shutdown components
      final Iterator componentIterator = my_activeComponents.entrySet().iterator();
      while (componentIterator.hasNext()) {
         final Map.Entry entry = (Map.Entry) componentIterator.next();
         try {
            ((ConstructComponent) entry.getValue()).shutdownComponent();
         } catch (ComponentRuntimeException e) {
            LOGGER.severe("Error shutting down " + (String) entry.getKey() + " component: "
                  + e.getMessage());
         } finally {
            ComponentRegistry.removeInstance((String) entry.getKey());
         }
      }
      // Remove component tabs from the gui
      if (my_gui != null) {
         my_gui.removeTabs();
      }
      // Await on executor shutdown completing
      try {
         my_executorService.awaitTermination(TEN, TimeUnit.SECONDS);
      } catch (InterruptedException e) {
         LOGGER.severe("Error shutting down component executor: " + e.getMessage());
      }

      if (my_executorService.isTerminated()) {
         LOGGER.fine("All components shut down correctly");
      } else {
         LOGGER.warning("Not all components shut down correctly");
      }
   }

   /**
    * This method is responsible for starting a ConStruct component and assigning it a logger.
    * A call is made to the component registry in order to instantiate the component using
    * reflection.
    * 
    * @param a_propertyName
    *           The property which identifies the class to load.
    * @param a_secondInterface
    *           The interface belonging to the specific component which the class must
    *           implement.
    * @return The instantiated component.
    * @throws ComponentInstantiationException
    *            if the class to be instantiated for one of the components cannot be found, if
    *            an error occurs while trying to instantiate a class for one of the components,
    *            or if an error occurs while trying to access a class for one of the
    *            components.
    * @throws InvalidComponentException
    *            If an instantiated class does not support the correct interfaces.
    */
   private ConstructComponent setupComponent(final String a_propertyName,
         final String a_secondInterface) throws ComponentInstantiationException,
         InvalidComponentException {

      final ConstructComponent component = ComponentRegistry.getInstance(a_propertyName,
            a_secondInterface, my_properties.getComponentProperties(a_secondInterface));
      // If the component has a component panel add it to the GUI.
      final JPanel componentPanel = component.getGraphicalInterface();
      if (componentPanel != null && my_gui != null) {
         my_gui.addTab(a_propertyName.substring(a_propertyName.lastIndexOf('.') + 1,
               a_propertyName.length()), componentPanel);
      }
      return component;
   }

   /**
    * This method is responsible for starting all of the ConStruct components. The information
    * extracted from the construct.properties file is used to determine which classes to
    * instantiate. This method also sets inter-component references and assigns access rights
    * (to the data store) to each component.
    * 
    * @throws ComponentInstantiationException
    *            if the class to be instantiated for one of the components cannot be found, if
    *            an error occurs while trying to instantiate a class for one of the components,
    *            or if an error occurs while trying to access a class for one of the
    *            components.
    * @throws InvalidComponentException
    *            If an instantiated class does not support the correct interfaces.
    * @throws NoSuchComponentException
    *            If an instantiated class cannot obtain a reference to a required component.
    */
   private void startupAllComponents() throws ComponentInstantiationException,
         InvalidComponentException, NoSuchComponentException {
      // Construct each component
      final Map componentMap = my_properties.getComponents();
      Iterator entries = componentMap.entrySet().iterator();
      // Construct all components
      while (entries.hasNext()) {
         final Map.Entry entry = (Map.Entry) entries.next();

         final ConstructComponent component = setupComponent((String) entry.getValue(),
               (String) entry.getKey());

         // Add to the component list
         my_activeComponents.put(entry.getKey(), component);
      }
      // Setup all component links
      final Iterator objects = my_activeComponents.values().iterator();
      while (objects.hasNext()) {
         final ConstructComponent component = (ConstructComponent) objects.next();
         component.setupComponentLinks();
      }
      // Start all components running
      entries = my_activeComponents.entrySet().iterator();
      while (entries.hasNext()) {
         final Map.Entry entry = (Map.Entry) entries.next();
         my_executorService.execute((ConstructComponent) entry.getValue());
      }
   }
}
