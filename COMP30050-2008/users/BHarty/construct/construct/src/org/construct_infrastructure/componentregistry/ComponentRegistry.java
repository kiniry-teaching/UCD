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
package org.construct_infrastructure.componentregistry;


import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import org.construct_infrastructure.component.ConstructComponent;

/**
 * This (singleton) class acts as a loader and registry for all the ConStruct components. All
 * access to construct components should be through this class.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class ComponentRegistry {

   /**
    * The variable which allows access to this class statically.
    */
   public static final ComponentRegistry REGISTRY = new ComponentRegistry();

   /**
    * The class name of the ConstructComponentInterface.
    */
   private static final String CPT_INTERFACE = "org.construct_infrastructure.component"
         + ".ConstructComponent";

   /**
    * The map that stores all the components, indexed by component name.
    */
   private static Map componentMap = new HashMap();

   /**
    * Private constructor used to stop instantiation of the registry. The ComponentRegistry
    * should be accessed statically.
    */
   private ComponentRegistry() {
      // Exists to prevent instantiation.
      super();
   }

   /**
    * Returns a reference to a specified component. If the component already exists, a
    * reference to that is returned. Otherwise a new component is instantiated.
    * 
    * @param a_classname
    *           The name of the class to instantiate if a component does not already exist.
    * @param a_secondaryInterface
    *           The interface that the newly instantiated class must implement.
    * @param some_properties
    *           The properties for this component.
    * @return The desired component.
    * @throws ComponentInstantiationException
    *            if the class to be instantiated for one of the components cannot be found, if
    *            an error occurs while trying to instantiate a class for one of the components,
    *            or if an error occurs while trying to access a class for one of the
    *            components.
    * @throws InvalidComponentException
    *            If an instantiated class does not support the correct interfaces.
    */
   public static synchronized ConstructComponent getInstance(final String a_classname,
         final String a_secondaryInterface, final Properties some_properties)
      throws ComponentInstantiationException, InvalidComponentException {
      // Check if we have already created an object for the given component
      ConstructComponent component = (ConstructComponent) componentMap
            .get(a_secondaryInterface);
      // If not, create a new instance of the component
      if (component == null) {
         component = createNewComponent(a_classname, a_secondaryInterface, some_properties);
      }
      return component;
   }

   /**
    * Creates a new constructy component.
    * 
    * @param a_classname
    *           the class we wist to instantiate.
    * @param a_secondaryInterface
    *           the service interface supported by the class.
    * @param some_properties
    *           the properties for this component.
    * @return the instantiated component.
    * @throws ComponentInstantiationException
    *            if the class to be instantiated for one of the components cannot be found, if
    *            an error occurs while trying to instantiate a class for one of the components,
    *            or if an error occurs while trying to access a class for one of the
    *            components.
    * @throws InvalidComponentException
    *            If an instantiated class does not support the correct interfaces.
    */
   private static ConstructComponent createNewComponent(final String a_classname,
         final String a_secondaryInterface, final Properties some_properties)
      throws InvalidComponentException, ComponentInstantiationException {
      ConstructComponent component;
      try {
         final Class cls = Class.forName(a_classname);
         // Check that the class implements the correct interfaces.
         if (!hasRequiredInterfaces(cls, a_secondaryInterface)) {
            throw new InvalidComponentException("The " + a_classname
                  + " component does not implement both the " + a_secondaryInterface
                  + " and the ConstructComponent interfaces");
         }
         final Class[] partypes = new Class[1];
         partypes[0] = Properties.class;
         final Constructor constructor = cls.getConstructor(partypes);
         final Object[] arglist = new Object[1];
         arglist[0] = some_properties;
         component = (ConstructComponent) constructor.newInstance(arglist);
         componentMap.put(a_secondaryInterface, component);
      } catch (ClassNotFoundException e) {
         throw new ComponentInstantiationException("Could not find the class for the "
               + a_secondaryInterface + " component: " + e.getMessage(), e.fillInStackTrace());
      } catch (InstantiationException e) {
         throw new ComponentInstantiationException("Could not instantiate the class for the "
               + a_secondaryInterface + " component: " + e.getMessage());
      } catch (IllegalAccessException e) {
         throw new ComponentInstantiationException("Could not access the class for the "
               + a_secondaryInterface + " component: " + e.getMessage());
      } catch (NoSuchMethodException e) {
         throw new ComponentInstantiationException(
               "Could not find necessary constructor component(Properties p) for the "
                     + a_secondaryInterface + " component: " + e.getMessage());
      } catch (InvocationTargetException e) {
         throw new ComponentInstantiationException("An error occured while "
               + "invoking constructor for the " + a_secondaryInterface + " component: "
               + e.getMessage());
      }
      return component;
   }

   /**
    * Adds a test component to the component registry. If a component with the given name
    * already exists, a it will not be overridden.
    * 
    * @param a_testComponent
    *           The test component to be added
    * @param a_secondaryInterface
    *           The interface that the newly instantiated class must implement.
    * @return true if the test component was added successfully, false if a component with the
    *         given name already exists.
    * @throws InvalidComponentException
    *            If an instantiated class does not support the correct interfaces.
    */
   public static synchronized boolean registerTestComponent(final String a_secondaryInterface,
         final ConstructComponent a_testComponent) throws InvalidComponentException {
      boolean result = false;
      componentMap.put(a_secondaryInterface, a_testComponent);
      result = true;
      return result;
   }

   /**
    * Removes a component from the registry.
    * 
    * @param a_componentName
    *           the name the component is registered with.
    */
   public static synchronized void removeInstance(final String a_componentName) {
      componentMap.remove(a_componentName);
   }

   /**
    * Returns a component from the registry.
    * 
    * @param a_componentInterface
    *           the name of the interface that the required componenrt extends and is
    *           registered with.
    * @return the component registered with the given interface name.
    * @throws NoSuchComponentException
    *            if a component with the given name does not exist.
    */
   public static synchronized ConstructComponent getComponent(
         final String a_componentInterface) throws NoSuchComponentException {
      final ConstructComponent component = (ConstructComponent) componentMap
            .get(a_componentInterface);
      if (component == null) {
         throw new NoSuchComponentException("There is no component with name "
               + a_componentInterface + "in the component registry");
      }
      return component;
   }

   /**
    * Iterates up the class hierarchy generating a list or all the interfaces implemented by a
    * given class.
    * 
    * @param a_class
    *           The class who's interfaces we wish to list.
    * @return A list containing the names of all this interfaces implemented by this class and
    *         its superclasses.
    */
   public static List getInterfaceList(final Class a_class) {
      final List interfaceNames = new ArrayList();
      final Class[] interfaces = a_class.getInterfaces();

      for (int i = 0; i < interfaces.length; i++) {
         interfaceNames.add(interfaces[i].getName());
      }

      // Check that we are not trying to instantiate an interface, then
      // recurse until we hit the the Object class
      if (!a_class.isInterface()
            && !a_class.getSuperclass().getName().equals("java.lang.Object")) {
         interfaceNames.addAll(0, getInterfaceList(a_class.getSuperclass()));
      }
      return interfaceNames;
   }

   /**
    * Checks if a given class implements both the construct component interface and the
    * component type interface.
    * 
    * @param a_class
    *           The class whose interfaces we wish to check
    * @param a_secondaryInterface
    *           The secondary component interface that this class should implement.
    * @return true if it implements the correct interfaces, false otherwise.
    */
   public static boolean hasRequiredInterfaces(final Class a_class,
         final String a_secondaryInterface) {
      final List interfaces = getInterfaceList(a_class);
      boolean foundPrimaryI = false;
      boolean foundSecondaryI = false;
      for (int i = 0; i < interfaces.size() && !(foundPrimaryI && foundSecondaryI); i++) {
         if (interfaces.get(i).equals(CPT_INTERFACE)) {
            foundPrimaryI = true;
         } else {
            if (interfaces.get(i).equals(a_secondaryInterface)) {
               foundSecondaryI = true;
            }
         }
      }
      return foundPrimaryI && foundSecondaryI;
   }
}
