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
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Hashtable;
import java.util.Map;
import java.util.Properties;
import java.util.logging.Logger;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/**
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie) This class extends the Property class
 *         load() method with additional functionality to check that all required properties
 *         are present.
 */
public class ConstructProperties extends Properties {

   /**
    * Serial version uniqueID.
    */
   private static final long serialVersionUID = 1L;

   /**
    * The logger for the property loaded
    */
   private static final Logger LOGGER = Logger
         .getLogger("org.construct_infrastructure.loader.ConstructProperties");

   /**
    * The level of detail to display logging messages.
    */
   private static String loggingLevel;

   /**
    * The hostname of the server.
    */
   private static String hostname;

   /**
    * A Map containing all the components to be started, keyed by their interfaces.
    */
   private final Map my_componentMap;

   /**
    * A Map containing the properties to be passed to each component, keyed by their
    * interfaces.
    */
   private final Map my_componentProps;

   /**
    * Creates an empty properties object.
    */
   public ConstructProperties() {
      super();
      my_componentMap = new Hashtable();
      my_componentProps = new Hashtable();
   }

   /**
    * Loads all the information required from the property file. An exception is thrown if
    * there is an error during loading. Note that this method does not check the validity of
    * property values.
    * 
    * @param the_propertiesFile
    *           The input stream containing data from the properties file.
    * @throws PropertyFileException
    *            if an error occurs accessing the property file, the property file contains an
    *            error or is missing a property.
    */
   public final void loadConstructProperties(final File the_propertiesFile)
         throws PropertyFileException {
      try {
         // Create a Document representation of the properties file
         final DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
         final DocumentBuilder builder = factory.newDocumentBuilder();
         Document document;
         try {
            document = builder.parse(the_propertiesFile);
         } catch (IOException e) {
            throw new PropertyFileException("Could not access the properties file: "
                  + e.getMessage(), e.fillInStackTrace());
         }

         // Get the root node
         Node rootNode;
         final NodeList nodeList = document.getElementsByTagName("construct");
         if (nodeList.getLength() == 1) {
            rootNode = nodeList.item(0);
         } else {
            throw new PropertyFileException(
                  "Single occurrence of root element \"construct\" not found");
         }
         // Get list of the children of the root node
         final NodeList childNodes = rootNode.getChildNodes();

         // Iterate through children.
         for (int i = 0; i < childNodes.getLength(); i++) {
            final Node child = childNodes.item(i);
            processNode(child);
         }
      } catch (ParserConfigurationException e) {
         throw new PropertyFileException("There was an error with the parser configuration");
      } catch (SAXException e) {
         throw new PropertyFileException("An error occured while parsing the file");
      }
   }

   /**
    * Processes the identity of a document node and passes it to the correct method for
    * processing.
    * 
    * @param a_child
    *           a Node representing either a component or global property.
    */
   private void processNode(final Node a_child) {
      // If child is a property, add it to the global property list.
      if (a_child.getNodeName().equals("property")
            && a_child.getAttributes().getNamedItem("name").getNodeValue() != null
            && a_child.getAttributes().getNamedItem("value").getNodeValue() != null) {
         processGlobalProperty(a_child);
      }
      // If child is a component, add details to the component map.
      if (a_child.getNodeName().equals("component")
            && a_child.getAttributes().getNamedItem("interface").getNodeValue() != null
            && a_child.getAttributes().getNamedItem("implementation").getNodeValue() != null) {
         processComponent(a_child);
      }
   }

   /**
    * Adds a global property to the global property list.
    * 
    * @param a_child
    *           a Node representing a global property.
    */
   private void processGlobalProperty(final Node a_child) {
      // Add property to the global property list.
      put(a_child.getAttributes().getNamedItem("name").getNodeValue(), a_child.getAttributes()
            .getNamedItem("value").getNodeValue());

      // Check for the loggingLevel property
      if (a_child.getAttributes().getNamedItem("name").getNodeValue().equals("loggingLevel")) {
         loggingLevel = a_child.getAttributes().getNamedItem("value").getNodeValue();
      }

      // Check for the hostname property
      if (a_child.getAttributes().getNamedItem("name").getNodeValue().equals("hostname")) {
         hostname = a_child.getAttributes().getNamedItem("value").getNodeValue();
      }
   }

   /**
    * Adds a component to the component map.
    * 
    * @param a_child
    *           a Node representing a component.
    */
   private void processComponent(final Node a_child) {
      // add details to the component map.
      my_componentMap.put(a_child.getAttributes().getNamedItem("interface").getNodeValue(),
            a_child.getAttributes().getNamedItem("implementation").getNodeValue());

      // Get component properties
      final Properties properties = new Properties();
      final NodeList componentChildren = a_child.getChildNodes();

      for (int k = 0; k < componentChildren.getLength(); k++) {
         final Node componentChild = componentChildren.item(k);
         if (componentChild.getNodeName().equals("property")
               && componentChild.getAttributes().getNamedItem("name").getNodeValue() != null
               && componentChild.getAttributes().getNamedItem("value").getNodeValue() != null) {
            properties.setProperty(componentChild.getAttributes().getNamedItem("name")
                  .getNodeValue(), componentChild.getAttributes().getNamedItem("value")
                  .getNodeValue());
         }
      }
      // Add properties to a map, indexed by component interface
      my_componentProps.put(a_child.getAttributes().getNamedItem("interface").getNodeValue(),
            properties);
   }

   /**
    * @return Returns the loggingLevel.
    */
   public static String getLoggingLevel() {
      return loggingLevel;
   }

   /**
    * @return Returns the hostname.
    */
   public static String getHostName() {
      return hostname;
   }

   /**
    * Tries to set the hostname. This will generally work on machines running windows, but not
    * linux. If this fails, the hostname will be set to 127.0.0.1 - which is usually an error.
    */
   public static void autoDetectHostName() {
      try {
         hostname = InetAddress.getLocalHost().getHostAddress();
      } catch (UnknownHostException e) {
         hostname = "127.0.0.1";
      }
   }

   /**
    * Returns the map of components contained in this property object.
    * 
    * @return a map of the components specified in this property object, keyed by interface
    *         name.
    */
   public final Map getComponents() {
      return my_componentMap;
   }

   /**
    * Get the set of properties associated with a component.
    * 
    * @param a_componentInterface
    *           the interface of the component who's properties are required
    * @return the set of Properties associated with the component.
    */
   public final Properties getComponentProperties(final String a_componentInterface) {
      return (Properties) my_componentProps.get(a_componentInterface);
   }
}
