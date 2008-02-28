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
import java.io.StringReader;
import java.util.concurrent.TimeoutException;

import org.construct_infrastructure.component.queryservice.QueryService;
import org.construct_infrastructure.io.Message;
import org.construct_infrastructure.io.Protocol;

import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.query.ResultSetFactory;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;

/**
 * This class acts as a proxy for contact the query service, abstracting the details of
 * discovery and communications from the developer.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class QueryServiceProxy extends AbstractClientProxy {

   /**
    * The active connection to the query service.
    */
   private SyncServiceWrapper my_queryServiceSocket;

   /**
    * Creates a new instance of the query service proxy.
    */
   public QueryServiceProxy() {
      super();
   }

   /**
    * Gets a connection to a QueryService.
    * 
    * @return a connection to a DataPort
    * @throws ServiceException
    *            if a connection could not be established.
    * @throws IOException
    *            if an error occurs adding the wrapper to the socket.
    */
   private SyncServiceWrapper getQueryServiceConnection() throws ServiceException, IOException {
      SyncServiceWrapper wrapper = null;
      if (my_queryServiceSocket != null && !my_queryServiceSocket.isClosed()
            && !my_queryServiceSocket.hasTimedOut()) {
         wrapper = my_queryServiceSocket;
      } else {
         wrapper = new SyncServiceWrapper(getService(QueryService.QS_NAME));
         my_queryServiceSocket = wrapper;
      }
      return wrapper;
   }

   /**
    * Sends a synchronous SPARQL query to Construct and constructs the response into a
    * ResultSet.
    * 
    * @param a_query
    *           the rdf to be added.
    * @throws ServiceException
    *            if a connection could not be established.
    * @throws IOException
    *            if an error occurs while contacting the query service.
    * @return the ResultSet object generated from thr query.
    */
   public ResultSet query(final String a_query) throws ServiceException, IOException {
      ResultSet resultSet = null;
      try {
         final SyncServiceWrapper queryService = getQueryServiceConnection();
         final Message response = queryService.writeToSocket(Protocol.format(a_query,
               Protocol.QUERY));
         if (response.getPayload().startsWith(Protocol.STATUS_ERROR)) {
            return null;
         } else {
            resultSet = createResultSet(response.getPayload());
         }
      } catch (IOException e) {
         close();
         throw e;
      } catch (TimeoutException e) {
         close();
         throw new IOException(e.getMessage());
      }
      return resultSet;
   }

   /**
    * Constructs an ResultSet object from an RDF string.
    * 
    * @param a_resultString
    *           the string containing the RDF representation of the result set
    * @return the ResultSet object created from the input string.
    */
   private ResultSet createResultSet(final String a_resultString) {
      ResultSet resultSet;
      // Create a result set
      final Model model = ModelFactory.createDefaultModel();
      final StringReader modelReader = new StringReader(a_resultString);
      model.read(modelReader, null, "N-TRIPLE");
      resultSet = ResultSetFactory.fromRDF(model);
      return resultSet;
   }

   /**
    * Shuts down any connections.
    * 
    * @throws IOException
    *            if an error occurs closing down connections to the query service.
    */
   public void close() throws IOException {
      if (my_queryServiceSocket != null) {
         my_queryServiceSocket.close();
      }
   }
}
