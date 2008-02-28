//
// $Revision: 7904 $: $Date: 2008-02-26 16:41:59 +0000 (Tue, 26 Feb 2008) $ - $Author: lorcan $
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
package org.construct_infrastructure.io;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.logging.Logger;

import com.thoughtworks.xstream.XStream;

/**
 * This class provides a meta-description of a service component to be made available via the
 * discovery service to the outside world. Examples of these components include the query
 * service and the data port. The objects should be constructed by service components and
 * passed to the registry service for publication to the outside world.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 */

public class ServiceComponentDescriptor implements Comparable {

   /**
    * Xstream converter use to marshal and unmarshal the descriptor.
    */
   private static final XStream XSTREAM;

   static {
      XSTREAM = new XStream();
      XSTREAM.alias("servicecomponentdescriptor", ServiceComponentDescriptor.class);
      XSTREAM.aliasField("name", ServiceComponentDescriptor.class, "my_name");
      XSTREAM.aliasField("description", ServiceComponentDescriptor.class, "my_description");
      XSTREAM.aliasField("host", ServiceComponentDescriptor.class, "my_host");
      XSTREAM.aliasField("port", ServiceComponentDescriptor.class, "my_port");
      XSTREAM.aliasField("misc", ServiceComponentDescriptor.class, "my_misc");
   }

   /**
    * The name of the component. This should be descriptive as the client-side developer will
    * read this to get a feel for what the service provides
    */
   private String my_name;

   /**
    * A description of the service including inputs and outputs for the client-side developer
    * to read and build interactions. This is essentially a human consumable description
    * similar to javadoc
    */
   private String my_description;

   /**
    * The name of the host that this service is running on.
    */
   private String my_host;

   /**
    * The port number that this service is running on.
    */
   private int my_port;

   /**
    * Any extra information about this service.
    */
   private String my_misc;

   /**
    * Constructor to create a new descriptor with all fields except the misc info filled out.
    * 
    * @param a_name
    *           the name of the service
    * @param a_description
    *           a description of the service
    * @param a_host
    *           the host on which the service is running
    * @param a_port
    *           the port that the service is running on
    */
   public ServiceComponentDescriptor(final String a_name, final String a_description,
         final String a_host, final int a_port) {
      my_name = a_name;
      my_description = a_description;
      my_host = a_host;
      my_port = a_port;
   }

   /**
    * Constructor to create a new descriptor with all fields filled out.
    * 
    * @param a_name
    *           the name of the service
    * @param a_description
    *           a description of the service
    * @param a_host
    *           the host on which the service is running
    * @param a_port
    *           the port that the service is running on
    * @param some_misc
    *           misc information about the service
    */
   public ServiceComponentDescriptor(final String a_name, final String a_description,
         final String a_host, final int a_port, final String some_misc) {
      this(a_name, a_description, a_host, a_port);
      my_misc = some_misc;
   }

   /**
    * @return Returns the description.
    */
   public final String getDescription() {
      return my_description;
   }

   /**
    * @return Returns the host.
    */
   public final String getHost() {
      return my_host;
   }

   /**
    * @return Returns the misc info.
    */
   public final String getMisc() {
      return my_misc;
   }

   /**
    * @return Returns the name.
    */
   public final String getName() {
      return my_name;
   }

   /**
    * @return Returns the port.
    */
   public final int getPort() {
      return my_port;
   }

   /**
    * Returns an XML representation of this object.
    * 
    * @return the XML representation
    */
   public final String marshall() {
      return XSTREAM.toXML(this);
   }

   /**
    * @param a_description
    *           The description to set.
    */
   public final void setDescription(final String a_description) {
      my_description = a_description;
   }

   /**
    * @param a_host
    *           The host to set.
    */
   public final void setHost(final String a_host) {
      my_host = a_host;
   }

   /**
    * @param some_misc
    *           The misc info to set.
    */
   public final void setMisc(final String some_misc) {
      my_misc = some_misc;
   }

   /**
    * @param a_name
    *           The a_name to set.
    */
   public final void setName(final String a_name) {
      my_name = a_name;
   }

   /**
    * @param a_port
    *           The port to set.
    */
   public final void setPort(final int a_port) {
      my_port = a_port;
   }

   /**
    * Method that takes some XML and tries to turn it into a ServiceComponentDescriptor object.
    * 
    * @param some_xml
    *           the XML to parse and convert into a ServiceComponentDescriptor object
    * @return the ServiceComponentDescriptor object
    */
   public static final ServiceComponentDescriptor unmarshal(final String some_xml) {
      return (ServiceComponentDescriptor) XSTREAM.fromXML(some_xml);
   }

   /**
    * Test equality of incoming object with this object. Two ServiceComponentDescriptors are
    * equal if the have the same name, description, host, port, and misc fields.
    * 
    * @param an_object
    *           the object to compare with this service descriptor
    * @return true if the service descriptors are equal, false otherwise.
    */
   public final boolean equals(final Object an_object) {
      // TODO STEVE - implement the hashcode method
      boolean isEqual = false;
      if (an_object instanceof ServiceComponentDescriptor) {
         final ServiceComponentDescriptor a_descriptor = (ServiceComponentDescriptor) an_object;
         isEqual = a_descriptor.getName().equals(my_name)
               && a_descriptor.getDescription().equals(my_description)
               && a_descriptor.getHost().equals(my_host) && a_descriptor.getPort() == my_port;
         if (a_descriptor.getMisc() != null) {
            isEqual = isEqual && a_descriptor.getMisc().equals(my_misc);
         }
      }
      return isEqual;
   }

   /**
    * This method prefers service component descriptors running on the localhost.
    * 
    * @param an_object
    *           the object to be compared.
    * @return 1 if only this service descriptor represents a service on the local host, -1 if
    *         only the compared descriptor represents a service running on the localhost, 0 in
    *         all other cases.
    */
   public final int compareTo(final Object an_object) {
      int result = 0;
      try {
         final String thisHost = InetAddress.getLocalHost().getCanonicalHostName();
         final String host1 = getHost();
         final String host2 = ((ServiceComponentDescriptor) an_object).getHost();
         // If we have no null values and at least one of the described hosts in this machine.
         if (thisHost != null && host1 != null && host2 != null
               && (host1.equals(thisHost) || host2.equals(thisHost))) {
            if (host1.equals(host2)) {
               result = 0;
            } else if (host1.equals(thisHost)) {
               result = -1;
            } else {
               result = 1;
            }
         }
      } catch (UnknownHostException e) {
         Logger.getLogger(getClass().getName()).warning(
               "UnknownHostException when comparing service descriptors: " + e.getMessage());
      }
      return result;
   }

   /**
    * Return a string version of this service descriptor. Current implementation just calls
    * marshall() method
    * 
    * @see ServiceComponentDescriptor#marshall();
    * @return a string version of this service descriptor.
    */
   public final String toString() {
      return marshall();
   }
}
