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
package org.construct_infrastructure.client;

import java.io.IOException;

import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.rdf.model.RDFNode;

/**
 * Tutorial 4: Asynchronous queries. This tutorial demonstrates the basics of working with
 * persistent queries.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class JavaAsyncWorldApp {

   /**
    * The number of responses received.
    */
   static int RESPONSE_COUNT = 0;

   /**
    * The query service proxy
    */
   public PersistentQueryServiceProxy pqsProxy;

   /**
    * The query used by this application
    */
   public static final String my_query = "SELECT ?subject WHERE{?subject <http://construct> \"world\" .}";

   /**
    * Set up response counter.
    */
   public JavaAsyncWorldApp() {
   }

   /**
    * Adds data to construct.
    * 
    * @return true on successful add, false otherwise
    * @throws ServiceException
    *            if the service cannot be found
    * @throws IOException
    *            if an error occurs contacting the service
    */
   public boolean submitData() throws ServiceException, IOException {
      // Send a VALID piece of RDF to the data store.
      final DataPortProxy dsProxy = new DataPortProxy();
      final boolean response = dsProxy.add("<http://hello><http://construct>\"world\".");
      dsProxy.close();
      return response;
   }

   /**
    * Blocks until results of the persistent query have been received a given number of times.
    * 
    * @param the_numberOfResponses
    *           how many responses we are waiting for
    * @throws InterruptedException
    *            if the wait is interrupted.
    */
   public synchronized void waitForResponse(int the_numberOfResponses)
         throws InterruptedException {
      while (RESPONSE_COUNT < the_numberOfResponses
            && pqsProxy.isPersistentQueryServiceActive()) {
         wait(500);
      }
   }

   /**
    * Adds a persistent query to Construct.
    * 
    * @throws ServiceException
    *            if the service cannot be found
    * @throws IOException
    *            if an error occurs contacting the service
    */
   public void submitQuery() throws ServiceException, IOException {
      try {
         // Create a Query Service Proxy Object
         pqsProxy = new PersistentQueryServiceProxy();
         JavaAsyncWorldApp handler = new JavaAsyncWorldApp();
         pqsProxy.setupAsyncQuery(my_query, "queryCallback", handler);
      } catch (NoSuchMethodException e) {
         System.err.println(e.getMessage());
      } catch (QueryAlreadyExistsException e) {
         System.err.println(e.getMessage());
      }
   }

   /**
    * Unsubscribes from a persistent query.
    * 
    * @throws ServiceException
    *            if the service cannot be found
    * @throws IOException
    *            if an error occurs contacting the service
    */
   public void unsubscribeFromQuery() throws ServiceException, IOException {
      pqsProxy.removeAsynchronousQuery(my_query);
   }

   /**
    * Stops the connection to the persistent query service.
    * 
    * @throws IOException
    *            if an error occurs shutting down the connection to the persistent query
    *            service.
    */
   public void shutdown() throws IOException {
      pqsProxy.close();
   }

   /**
    * A main method that submits data to construct and sets up an asynchronous query.
    * 
    * @param some_args
    *           not used.
    */
   public static void main(final String[] some_args) {
      JavaAsyncWorldApp app = new JavaAsyncWorldApp();
      try {
         System.err.println("Submitting data");
         app.submitData();
         System.err.println("Submitting query");
         app.submitQuery();
         System.err.println("Waiting for 2 responses");
         app.waitForResponse(2);
         System.err.println("Unsubscribing from query");
         app.unsubscribeFromQuery();
         System.err.println("Exiting");
         app.shutdown();
      } catch (ServiceException e) {
         System.err.println(e.getMessage());
      } catch (IOException e) {
         System.err.println(e.getMessage());
      }
         catch (InterruptedException e) {
         System.err.println(e.getMessage());
      }
   }

   /**
    * Print out the results of the query and incrament the counter.
    * 
    * @param a_resultSet
    *           the results of the query.
    */
   public void queryCallback(ResultSet a_resultSet) {
      // Check the result set. Null indicates that an error occured.
      if (a_resultSet != null) {
         // Iterate through the solutions and print them out.
         // There should be one solution produced from the above query.
         while (a_resultSet.hasNext()) {
            final QuerySolution solution = a_resultSet.nextSolution();
            final RDFNode rdfnode = solution.get("subject");
            System.out.println("A solution is: " + rdfnode.toString());
         }
      } else {
         System.err.println("The query did not execute successfully");
      }
      RESPONSE_COUNT++; // Incrament the response counter.
   }
}
