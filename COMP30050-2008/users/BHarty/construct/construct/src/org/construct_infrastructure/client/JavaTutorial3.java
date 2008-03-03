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

import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.rdf.model.Literal;

/**
 * Tutorial 3: SPARQL and the Query Service. This tutorial demonstrates the basics of querying
 * construct with the aid of the QueryServiceProxy, and using the Jena ResultSet class to
 * examine solutions.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class JavaTutorial3 {
   /**
    * A main method that queries construct and examines the solutions returned using a Jena
    * ResultSet.
    * 
    * @param some_args
    *           not used.
    * @throws ServiceException
    *            if a data port cannot be found.
    * @throws IOException
    *            if an error occurs while talking to the data port, or if the local proxy is not running.
    */
   public static void main(final String[] some_args) throws ServiceException, IOException {

      // Create a Query Service Proxy Object
      final QueryServiceProxy qsProxy = new QueryServiceProxy();

      // Construct the SPARQL query to find the name belonging to http://example.com/people/bob
      final String query = "SELECT ?name WHERE{<http://example.com/people/bob> <http://example.com/terms#name> ?name}";
      
      // Submit the query to construct.
      final ResultSet resultSet = qsProxy.query(query);

      // Print out the solution
      if (resultSet.hasNext()) {
         final QuerySolution solution = resultSet.nextSolution();
         final Literal name = solution.getLiteral("name");
         System.out.println(name.toString());
      } else {
         System.err.println("The query did not return any results");
      }

      // Close the connection to the query service.
      qsProxy.close();

   }
}
