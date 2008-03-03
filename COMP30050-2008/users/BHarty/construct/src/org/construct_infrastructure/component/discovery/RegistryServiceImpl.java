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
package org.construct_infrastructure.component.discovery;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.io.ServiceComponentDescriptor;

/**
 * Class that holds information on registered services.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 */
public class RegistryServiceImpl extends AbstractConstructComponent implements RegistryService {

   /**
    * The services are stored in a map datastructure here.
    */
   private final Map my_services;

   /**
    * Default constructor just initialised members.
    * 
    * @param some_properties
    *           the properties file for this component.
    */
   public RegistryServiceImpl(final Properties some_properties) {
      super();
      setProperties(some_properties);
      my_services = new HashMap();
   }

   /**
    * Method to be used when registering a service. If a service with the same name already
    * exists is will be overwritten.
    * 
    * @param a_description
    *           the service to be regsitered with this regirsty
    */
   public final void registerService(final ServiceComponentDescriptor a_description) {
      my_services.put(a_description.getName(), a_description);
   }

   /**
    * Checks registry to see if the service already exists and has been registered.
    * 
    * @param the_name
    *           the name of the service to look for
    * @return has the service already been registered
    */
   public final boolean serviceExists(final String the_name) {
      return my_services.containsKey(the_name);
   }

   /**
    * Removes the given service from the registry if it exists.
    * 
    * @param the_name
    *           of the service to remove
    */
   public final void removeService(final String the_name) {
      my_services.remove(the_name);
   }

   /**
    * Get an interator over the service descriptions.
    * 
    * @return iterator of the service descriptions
    */
   public final Iterator serviceDescriptorIterator() {
      return my_services.values().iterator();
   }

   /**
    * Get the named service or return null if it does not exist.
    * 
    * @param the_name
    *           the name of the service to get
    * @return teh service descriprot with the given name or null if it does not exist
    */
   public final ServiceComponentDescriptor getService(String the_name) {
      return (ServiceComponentDescriptor) my_services.get(the_name);
   }

   /**
    * Empty method - we don't need to set up and links.
    */
   public final void setupComponentLinks() {
      // Empty method
   }

   /**
    * Empty method - we don't need to do anything on run.
    */
   public final void onRun() {
      // Empty method
   }

   /**
    * Empty method - we don't need to do anything on shutdown.
    */
   public void onShutdown() {
      // Empty method
   }

}
