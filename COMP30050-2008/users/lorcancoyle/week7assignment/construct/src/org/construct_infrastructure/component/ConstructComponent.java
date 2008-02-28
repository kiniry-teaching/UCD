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


import java.util.logging.Logger;

import javax.swing.JPanel;

import org.construct_infrastructure.componentregistry.NoSuchComponentException;

/**
 * This interface defines the basic methods which must be implemented by all construct
 * components. These methods are used by the construct component loader in order to setup and
 * shutdown components.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public interface ConstructComponent extends Runnable {

   /**
    * Called in order to shutdown a component. Implementing components should ensure that this
    * method performs any cleanup operations and then terminates. This method should not throw
    * an exception. If there is any risk of a component throwing an exception during shutdown,
    * it should be wrapped inside a ComponentRuntimeException.
    * 
    */
   void shutdownComponent();

   /**
    * Gives access to the JPanel interface defined by this component.
    * 
    * @return the JPanel interface for this component, or null if no interface has been defined
    */
   JPanel getGraphicalInterface();

   /**
    * Sets the JPanel which makes up the interface for this component. Null values are valid.
    * 
    * @param a_componentPanel
    *           The JPanel interface for this component.
    */
   void setGraphicalInterface(JPanel a_componentPanel);

   /**
    * Subclasses should use this method to gain references to other components they interact
    * with from the component registry. This method is called after component construction, but
    * before the run method is called.
    * 
    * @throws NoSuchComponentException
    *            if an attempt is made to access a component which doesnt exist.
    */
   void setupComponentLinks() throws NoSuchComponentException;

   /**
    * Gives access to the logger for the component.
    * 
    * @return The logger for this component.
    */
   Logger getLogger();
}
