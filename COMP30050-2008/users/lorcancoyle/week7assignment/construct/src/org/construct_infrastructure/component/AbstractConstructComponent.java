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
package org.construct_infrastructure.component;


import java.util.Properties;
import java.util.logging.Level;
import java.util.logging.Logger;

import javax.swing.JPanel;

import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.loader.ConstructProperties;

/**
 * This class provides a default implementation for the methods defined in the
 * ConstructComponent interface. Subclasses may provide custom implementations if desired.
 * Subclasses should make a call to the constructor in this class.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public abstract class AbstractConstructComponent implements ConstructComponent {

   /**
    * How often does the run method check to see if the component should shutdown?
    */
   private static final int SHUTDOWN_CHECK_DELAY = 500;

   /**
    * The component gui interface.
    */
   private transient JPanel my_componentPanel;

   /**
    * The logger for this class.
    */
   private final Logger my_logger;

   /**
    * The properties associated with the component, passed in on initialisation.
    */
   private Properties my_properties;

   /**
    * Whether or not this component should shutdown.
    */
   private boolean my_shouldShutdown;

   /**
    * The constructor is responsible for creating a logger for the component.
    */
   public AbstractConstructComponent() {
      super();
      // Set up the logger
      my_logger = Logger.getLogger(getClass().getName());
      getLogger().setLevel(Level.parse(ConstructProperties.getLoggingLevel()));
      my_shouldShutdown = false;
   }

   /**
    * Returns this component's JPanel interface. May be null.
    * 
    * @return the components gui panel, or null if it does not have one.
    */
   public final JPanel getGraphicalInterface() {
      return my_componentPanel;
   }

   /**
    * Gives access to the logger for the component.
    * 
    * @return The logger for this component.
    */
   public final Logger getLogger() {
      return my_logger;
   }

   /**
    * Get the properties associated with the component.
    * 
    * @return The properties for this component.
    */
   protected final Properties getProperties() {
      return my_properties;
   }

   /**
    * This template method can be implemented by subclasses to provide functionality at the
    * start of the run method. Developers should ensure that this method terminates and does
    * not throw an exception. If you want to expose this Component as a service to the outside
    * world you must register it with the ResgistryService.
    * 
    */
   public abstract void onRun();

   /**
    * This template method can be implemented by subclasses to provide functionality on
    * shutdown. Developers should ensure that this method terminates and does not throw an
    * exception.
    */
   public abstract void onShutdown();

   /**
    * The run method method will keep the object active until the shutdown method is called by
    * the component loader.
    */
   public final void run() {
      onRun();
      synchronized (this) {
         try {
            while (!my_shouldShutdown) {
               wait(SHUTDOWN_CHECK_DELAY);
            }
         } catch (InterruptedException e) {
            my_logger.severe("Component runtime error: " + e.getMessage());
         }
      }
   }

   /**
    * Sets this component's JPanel interface. This should be called in the constructor.
    * 
    * @param a_componentPanel
    *           the interface for this component.
    */
   public final void setGraphicalInterface(final JPanel a_componentPanel) {
      my_componentPanel = a_componentPanel;
   }

   /**
    * Sets this component's properties as specified in the construct.properties file. This
    * should be called in the constructor if a component requires later access to their
    * properties.
    * 
    * @param some_properties
    *           The properties class for this component.
    */
   protected final void setProperties(final Properties some_properties) {
      my_properties = some_properties;
   }

   /**
    * This template method should be called by subclasses that need to gain references to other
    * components from the component registry.
    * 
    * @throws NoSuchComponentException
    *            if an attempt is made to access a component which doesnt exist.
    */
   public abstract void setupComponentLinks() throws NoSuchComponentException;

   /**
    * Whether or not this component has been instructed to shutdown.
    * 
    * @return true if this component has been asked to shutdown, false otherwise.
    */
   protected final boolean shouldShutdown() {
      return my_shouldShutdown;
   }

   /**
    * Instructs the component to stop operation. The method will call the component's
    * onShutdown() method and then notify the run method to terminate by setting a flag.
    */
   public final void shutdownComponent() {
      onShutdown();
      my_shouldShutdown = true;
   }

}
