//
// $Revision: 7871 $: $Date: 2008-02-25 15:06:55 +0000 (Mon, 25 Feb 2008) $ - $Author:
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
package org.construct_infrastructure.client;

import java.io.IOException;

/**
 * Tutorial 1: Sending an RDF statement to the Data Port. This tutorial shows the basics of
 * connecting to Construct using the provided Java client libraries.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */

public final class JavaTutorial1 {

   /**
    * A main method that constructs 2 RDF statements and attempts to add them to Construct
    * using the proxy.
    * 
    * @param some_args
    *           not used.
    * @throws ServiceException
    *            if a data port cannot be found.
    * @throws IOException
    *            if an error occurs while talking to the data port, or if the local proxy is not running.
    */
   public static void main(final String[] some_args) throws ServiceException, IOException {
      // Create a connection to a Construct DataPort on the network
      final DataPortProxy proxy = new DataPortProxy();

      // Send a VALID piece of RDF to the data store
      boolean response = proxy
            .add("<http://example.com/people/bob><http://example.com/terms#name>\"Bob Smith\".");
      System.out.println(response); // response should be "true"

      // Send an INVALID piece of RDF to the data store;
      response = proxy.add("http://badly<http://formed>\"rd\"f\".");
      System.out.println(response); // response should be "false"

      // Close the connection to the data port
      proxy.close();
   }
}
