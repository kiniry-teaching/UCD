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


import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.concurrent.TimeoutException;

import org.construct_infrastructure.component.dataport.DataPort;
import org.construct_infrastructure.io.Message;
import org.construct_infrastructure.io.Protocol;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.shared.Lock;

/**
 * This class acts as a proxy for contact the data port, abstraction the details of discovery
 * and communications from the developer.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class DataPortProxy extends AbstractClientProxy {

   /**
    * The active connection to the data port.
    */
   private SyncServiceWrapper my_dataPortSocket;

   /**
    * Creates a new instance of the data port proxy and starts scanning for Construct
    * instances.
    */
   public DataPortProxy() {
      super();
   }

   /**
    * Gets a connection to a DataPort.
    * 
    * @return a connection to a DataPort
    * @throws ServiceException
    *            if a connection could not be established.
    * @throws IOException
    *            if an error occurs adding the wrapper to the socket.
    */
   private SyncServiceWrapper getDataPortConnection() throws ServiceException, IOException {
      SyncServiceWrapper wrapper = null;
      if (my_dataPortSocket != null && !my_dataPortSocket.isClosed()
            && !my_dataPortSocket.hasTimedOut()) {
         wrapper = my_dataPortSocket;
      } else {
         if (my_dataPortSocket != null && my_dataPortSocket.hasTimedOut()) {
            System.out.println("Socket timed out - opening new socket");
         }
         wrapper = new SyncServiceWrapper(getService(DataPort.DP_NAME));
         my_dataPortSocket = wrapper;
      }
      return wrapper;
   }

   /**
    * Adds some RDF to Construct with the specified expiry time.
    * 
    * @param some_rdf
    *           the rdf to be added
    * @param an_expiryTime
    *           the expiry time associated with the RDF.
    * @throws ServiceException
    *            if a connection could not be established.
    * @throws IOException
    *            if an error occurs while contacting the data port
    * @return true if data was added successfully, false otherwise.
    */
   public boolean add(final String some_rdf, final long an_expiryTime)
         throws ServiceException, IOException {
      return add(some_rdf + new Long(an_expiryTime).toString());
   }

   /**
    * Adds some RDF to Construct.
    * 
    * @param some_rdf
    *           the rdf to be added.
    * @throws ServiceException
    *            if a connection could not be established.
    * @throws IOException
    *            if an error occurs while contacting the data port
    * @return true if data was added successfully, false otherwise.
    */
   public boolean add(final String some_rdf) throws ServiceException, IOException {
      boolean returnValue = false;
      final SyncServiceWrapper dataPort = getDataPortConnection();
      try {
         final Message response = dataPort.writeToSocket(Protocol.format(some_rdf,
               Protocol.RDF_ADD));
         returnValue = response.getPayload().startsWith(Protocol.STATUS_OK);
      } catch (TimeoutException e) {
         close();
         throw new IOException(e.getMessage());
      }

      return returnValue;
   }

   /**
    * Adds the data contained in a Jena Model to Construct.
    * 
    * @param a_model
    *           The Jena model to be added to Construt.
    * @throws ServiceException
    *            if a connection could not be established.
    * @throws IOException
    *            if an error occurs while contacting the data port
    * @return true if data was added successfully, false otherwise.
    */
   public boolean add(final Model a_model) throws ServiceException, IOException {
      return add(modelToNtriples(a_model));
   }

   /**
    * Adds the data contained in a Jena Model to Construct with an expiry time. *
    * 
    * @param a_model
    *           The Jena model to be added to Construt.
    * @param a_time
    *           the expiry time for this data in ms.
    * @throws ServiceException
    *            if a connection could not be established.
    * @throws IOException
    *            if an error occurs while contacting the data port
    * @return true if data was added successfully, false otherwise.
    */
   public boolean add(final Model a_model, final long a_time) throws ServiceException,
         IOException {
      return add(modelToNtriples(a_model), a_time);
   }

   /**
    * Converts a model to N-TRIPLES.
    * 
    * @param a_model
    *           the model to be converted to N-TRIPLEs.
    * @return the N-TRIPLE representation of the model
    */
   private String modelToNtriples(final Model a_model) {
      if (a_model == null) {
         throw new IllegalArgumentException("Model is null");
      }
      String data = "";
      try {
         a_model.enterCriticalSection(Lock.READ);
         final ByteArrayOutputStream byteOutStream = new ByteArrayOutputStream();
         a_model.write(byteOutStream, "N-TRIPLE");
         final String[] ntriples = byteOutStream.toString().split("\n");
         for (int i = 0; i < ntriples.length; i++) {
            data = data + ntriples[i].trim(); // this is here as a windows hack. Jena will
            // put a \r as part of the newline so we need
            // to remove it
         }
      } finally {
         a_model.leaveCriticalSection();
      }
      return data;
   }

   /**
    * Close the data port socket if it is still open.
    * 
    * @throws Throwable -
    *            all thrown exceptions ignored.
    */
   protected void finalize() throws Throwable {
      try {
         if (my_dataPortSocket != null) {
            my_dataPortSocket.close();
         }
      } finally {
         super.finalize();
      }
   }

   /**
    * Shuts down any connections.
    * 
    * @throws IOException
    *            if an error occurs closing down connections to the query service.
    */
   public void close() throws IOException {
      if (my_dataPortSocket != null) {
         my_dataPortSocket.close();
      }
   }

}
