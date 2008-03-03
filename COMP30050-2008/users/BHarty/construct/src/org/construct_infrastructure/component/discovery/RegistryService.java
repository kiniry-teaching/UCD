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


import java.util.Iterator;

import org.construct_infrastructure.component.ConstructComponent;
import org.construct_infrastructure.io.ServiceComponentDescriptor;

/**
 * Interface describing the service registry service.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 *
 */
public interface RegistryService extends ConstructComponent {

   /**
    * Register a service with this method.
    * @param a_description the description of the service
    */
   void registerService(final ServiceComponentDescriptor a_description);
   
   /**
    * Checks registry to see if the service already exists and has been registered.
    * @param the_name the name of the service to look for
    * @return has the service already been registered
    */
   boolean serviceExists(String the_name);
   
   /**
    * Removes the given service from the registry if it exists.
    * @param the_name of the service to remove
    */
   void removeService(String the_name);

   /**
    * Get an interator over the service descriptions.
    * @return iterator of the service descriptions 
    */
   Iterator serviceDescriptorIterator();
   
   /**
    * Get the named service or return null if it does not exist.
    * @param the_name the name of the service to get
    * @return teh service descriprot with the given name or null if it does not exist
    */
   ServiceComponentDescriptor getService(String the_name);

}
