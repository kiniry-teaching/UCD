//
// $Revision: 7810 $: $Date: 2008-02-20 17:51:52 +0000 (Wed, 20 Feb 2008) $ - $Author: gstevenson $
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
package org.construct_infrastructure.component.gossiping;


import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.URLEncoder;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.component.datastorage.DataStoreManager;
import org.construct_infrastructure.component.datastorage.MetaData;
import org.construct_infrastructure.component.datastorage.observable.DataStoreObserver;
import org.construct_infrastructure.component.datastorage.observable.ObservableDataStore;
import org.construct_infrastructure.component.gossiping.buffer.BufferManager;
import org.construct_infrastructure.component.gossiping.buffer.Summary;
import org.construct_infrastructure.component.gossiping.membership.Contact;
import org.construct_infrastructure.component.gossiping.membership.MembershipManager;
import org.construct_infrastructure.component.gossiping.util.StuffedByteArrayIterator;
import org.construct_infrastructure.component.gossiping.util.StuffedByteArrayOutputStream;
import org.construct_infrastructure.component.gossiping.util.TransformationException;
import org.construct_infrastructure.component.network.NetworkManager;
import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.RDFNode;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.Statement;
import com.hp.hpl.jena.rdf.model.StmtIterator;

/**
 * The GossipManager provides a base implementation of a gossip manager.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 * 
 */
public class GossipManagerImpl extends AbstractConstructComponent implements GossipManager,
      DataStoreObserver {

   /**
    * The header byte for a message buffer summary packet.
    */
   public static final byte SUMMARY_HEADER = 0x00;

   /**
    * The header byte for a data message packet.
    */
   public static final byte DATA_HEADER = 0x01;

   /**
    * The header byte for a message request packet.
    */
   public static final byte REQUEST_HEADER = 0x02;

   /**
    * The default gossiping period (in milliseconds) between rounds.
    */
   // GRAHAM: Load this from properties
   private static final int GOSSIP_PERIOD = 5000;

   /**
    * The interface for the datastore manager.
    */
   private static final String DATASTORE_MANAGER
      = "org.construct_infrastructure.component.datastorage.DataStoreManager";

   /**
    * The interface for the network manager.
    */
   private static final String NETWORK_MANAGER
      = "org.construct_infrastructure.component.network.NetworkManager";

   /**
    * The interface for the membership manager.
    */
   private static final String MEMBERSHIP_MANAGER
      = "org.construct_infrastructure.component.gossiping.membership.MembershipManager";

   /**
    * The interface for the buffer manager.
    */
   private static final String BUFFER_MANAGER
      = "org.construct_infrastructure.component.gossiping.buffer.BufferManager";

   /**
    * The datastore manager component.
    */
   private DataStoreManager my_dataStoreManager;

   /**
    * The network manager component.
    */
   private NetworkManager my_networkManager;

   /**
    * The membership manager component.
    */
   private MembershipManager my_membershipManager;

   /**
    * The buffer manager component.
    */
   private BufferManager my_bufferManager;

   /**
    * The thread responsible for initiating gossip sessions from this node.
    */
   private final GossipThread my_gossipThread;

   /**
    * The queue which buffers and aggregates messages which arrive close
    * together.
    */
   private final MessageQueue my_messageQueue;

   /**
    * Initialise the gossip manager.
    * 
    * @param some_properties
    *           Properties for the gossip manager.
    */
   public GossipManagerImpl(final Properties some_properties) {
      super();
      setProperties(some_properties);
      my_gossipThread = new GossipThread(GOSSIP_PERIOD);
      my_messageQueue = new MessageQueue(this);
   }

   /**
    * This method is called whenever statements are added to the data store is
    * changed.
    * 
    * @param a_mode
    *           Indicates whether a statement has been added or deleted.
    * @param some_statements
    *           RDF statements that have been added to the data store in
    *           N-TRIPLE format.
    * @param some_metadata
    *           RDF meta-data statements in N-TRIPLE format associated with the
    *           statements.
    * @param the_origin
    *           The origin of the data.
    * @see org.construct_infrastructure.component.datastorage.observable.DataStoreObserver#
    *      update(java.lang.String, java.lang.String)
    */
   public final void update(final int a_mode, final String some_statements,
         final String some_metadata, final Object the_origin) {
      if ((the_origin != this) && (a_mode == ObservableDataStore.ADDED)) {
         my_messageQueue.addToQueue(some_statements, some_metadata);
      }
   }

   /**
    * Disseminate a message around the network of construct nodes. Applications
    * should call this method to send a message.
    * 
    * @param a_message
    *           The message to disseminate.
    */
   public final void gossipMessage(final Message a_message) {
      // Create metadata for the message
      final Map metadata = new HashMap();
      metadata.put("Buffer timer", new Integer(0));
      metadata.put("Entry time", new Long(System.currentTimeMillis()));

      // Add the message to the message buffer
      my_bufferManager.messageReceived(a_message, metadata);

      // GRAHAM: Allow subclasses the opportunity of doing something when we
      // receive a message to gossip:
      // onGossipMessage(a_message);

      // GRAHAM: Note that we don't actually send the message - we're using
      // gossip-pull so it's only sent when requested. Perhaps we could
      // experiment with sending the message to a number of peers when it is
      // first injected into the system (i.e. here). If I could measure TTL for
      // peers in the membership list I could use that to choose a couple of far
      // off members and see what happens...
   }

   /**
    * Notification from the network manager that some gossip has been received
    * from the given source.
    * 
    * @param the_source
    *           The source of the gossip.
    * @param a_replyAddress
    *           The address of the contact to reply to, should a reply be
    *           required.
    * @param some_rawGossip
    *           The raw bytes received which represent the received message.
    */
   public final void receivedGossip(final Contact the_source, final Contact a_replyAddress,
         final byte[] some_rawGossip) {
      // Check on the type of message:
      // (i) it's a summary
      //        compare with our summary and request missing messages
      // (ii) it's a data message
      //        add it to the buffer then deliver
      // (iii) it's a request for one of the messages in the buffer
      //        get the message from the buffer and send it

      // GRAHAM: make this extensible by somehow allowing objects to register
      // handlers for a given message type.

      final byte header = some_rawGossip[0];
      final byte[] data = new byte[some_rawGossip.length - 1];
      System.arraycopy(some_rawGossip, 1, data, 0, some_rawGossip.length - 1);

      switch (header) {
         case SUMMARY_HEADER:
            handleSummaryPacket(a_replyAddress, data);
            break;
         case DATA_HEADER:
            handleDataPacket(data);
            break;
         case REQUEST_HEADER:
            handleRequestPacket(a_replyAddress, data);
            break;
         default:
            getLogger().warning(
                  "Unknown gossip PDU message header [" + header + "]: discarding message.");
            break;
      }
   }

   /**
    * Handle a packet which contains a message buffer summary. Compare with our
    * message buffer and request missing messages.
    * 
    * @param a_replyAddress
    *           Where to request missing messages from.
    * @param some_data
    *           The raw byte data of the summary.
    */
   private void handleSummaryPacket(final Contact a_replyAddress, final byte[] some_data) {
      try {
         final Summary summary = new Summary(some_data);
         final MessageID recommendedID = my_bufferManager.recommendMessage(summary);
         if (recommendedID != null) {
            requestMessage(a_replyAddress, recommendedID);
         }
      } catch (TransformationException e) {
         getLogger().warning("Unable to deserialize summary packet.");
      }
   }

   /**
    * Handle a packet which contains an application data message. Deserialize
    * the message, add it to the message buffer, and then deliver the message.
    * 
    * @param some_rawData
    *           The raw bytes of the data packet.
    */
   private void handleDataPacket(final byte[] some_rawData) {
      try {
         final StuffedByteArrayIterator iterator = new StuffedByteArrayIterator(some_rawData);
         final int bufferTimer = Integer.parseInt(new String(iterator.nextSection()));
         final long remoteTime = Long.parseLong(new String(iterator.nextSection()));
         final StringMessage dataMessage = new StringMessage(iterator.nextSection());

         final Map metadata = new HashMap();
         metadata.put("Buffer timer", new Integer(bufferTimer));
         metadata.put("Entry time", new Long(System.currentTimeMillis()));

         my_bufferManager.messageReceived(dataMessage, metadata);
         merge(dataMessage, bufferTimer, remoteTime);
      } catch (TransformationException e) {
         getLogger().warning("Unable to deserialize data packet." + e);
      } catch (IOException e) {
         getLogger().warning("Unexpected end of message!" + e);
      } catch (NumberFormatException e) {
         getLogger().warning("Unable to deserialise illegal message format." + e);
      }

   }

   /**
    * Merge the data from the given message into the datastore, adjusting the
    * expiry timer metadata as necessary.
    * 
    * @param a_dataMessage
    *           The message to merge
    * @param the_bufferTimer
    *           The cumulative time the message has spent buffered
    * @param the_remoteTime
    *           The time on the remote machine
    */
   private void merge(final StringMessage a_dataMessage, final int the_bufferTimer,
         final long the_remoteTime) {
      // Read the data into Jena models
      final Model model = ModelFactory.createDefaultModel();
      model.read(new ByteArrayInputStream(a_dataMessage.getModel().getBytes()), null,
            "N-TRIPLE");
      final Model metadata = ModelFactory.createDefaultModel();
      metadata.read(new ByteArrayInputStream(a_dataMessage.getMetadata().getBytes()), null,
            "N-TRIPLE");

      // Iterate through each statement and adjusts it's expiry timer
      final StmtIterator iterator = model.listStatements();
      while (iterator.hasNext()) {
         final Statement statement = iterator.nextStatement();
         adjustStatementExpiry(statement, metadata, the_bufferTimer);
      }

      // Pass to the datastore
      my_dataStoreManager.addStatementsWithMetadata(modelToNtriples(model),
            modelToNtriples(metadata), this);
   }

   /**
    * Converts a model to N-TRIPLES.
    * 
    * @param a_model
    *           The model to convert.
    * @return The model in N-TRIPLE format.
    */
   private String modelToNtriples(final Model a_model) {
      final ByteArrayOutputStream byteOutStream = new ByteArrayOutputStream();
      a_model.write(byteOutStream, "N-TRIPLE");
      return byteOutStream.toString();
   }

   /**
    * Adjust the expiry timer of a given statement in the metadata model.
    * 
    * @param a_statement
    *           The statement to adjust.
    * @param some_metadata
    *           The metadata to adjust.
    * @param the_adjustment
    *           The amount of time to subtract.
    */
   private void adjustStatementExpiry(final Statement a_statement, final Model some_metadata,
         final long the_adjustment) {
      final Resource subject = a_statement.getSubject();
      final Property predicate = a_statement.getPredicate();
      final RDFNode object = a_statement.getObject();
      // Reconstruct the statement guid from a concatenation of
      // subject, predicate and object fields.
      final String statementGUID = constructStmtGuid(subject, predicate, object);
      // Find associated meta-data statement
      final Resource metaDataResource = some_metadata.getResource(MetaData.SUBJECT_PREFIX
            + statementGUID);
      final Statement propertyStatement = metaDataResource
            .getProperty(MetaData.EXPIRY_COUNTDOWN);
      // make sure we have it in our metadata before attempting to update it
      if (propertyStatement != null) {
         final String expiryTimerString = propertyStatement.getObject().toString();
         long expiryTimer = Long.parseLong(expiryTimerString);
         // Update the expiry time
         expiryTimer -= the_adjustment;
         // Update the statement
         propertyStatement.changeObject(expiryTimer);
      } else {
         getLogger()
               .warning("Received statement without expiry time metadata: " + a_statement);
      }
   }

   /**
    * This method constructs a meta-ID from the parts of a Statement.
    * 
    * @param a_subject
    *           the subject we are interested in.
    * @param a_predicate
    *           the predicate linking the subject and object.
    * @param an_object
    *           the object we are interested in.
    * @return the meta-id for the given Statement.
    */
   private String constructStmtGuid(final Resource a_subject, final Property a_predicate,
         final RDFNode an_object) {
      String result = "";
      try {
         result = URLEncoder.encode((a_subject.toString() + a_predicate.toString() + an_object
               .toString()), "UTF-8");
      } catch (UnsupportedEncodingException an_exception) {
         getLogger().warning(an_exception.getMessage());
      }
      return result;
   }

   /**
    * Handle a packet which contains a message request. Get the message from the
    * buffer and send it to the requester.
    * 
    * @param a_replyAddress
    *           Where to send the message.
    * @param some_data
    *           The raw bytes of the message ID requested.
    */
   private void handleRequestPacket(final Contact a_replyAddress, final byte[] some_data) {
      // GRAHAM: Limit the number of requests we fulfil in a given time period
      // (to stop us being overloaded). Not sure how we'll implement that one.
      try {
         final MessageID requestID = new MessageID(some_data);
         final Message replyMessage = my_bufferManager.get(requestID);
         if (replyMessage == null) {
            getLogger().warning(
                  "Request for message which does not exist in the buffer: " + requestID);
         } else {
            sendMessage(a_replyAddress, replyMessage);
         }
      } catch (TransformationException e) {
         getLogger().warning("Unable to deserialize requested message ID.");
      }
   }

   /**
    * Request a message from a given source.
    * 
    * @param the_source
    *           The source to request from.
    * @param the_id
    *           The ID of the message to request.
    */
   protected final void requestMessage(final Contact the_source, final MessageID the_id) {
      sendGossipingPDU(the_source, REQUEST_HEADER, the_id.serialize());
   }

   /**
    * Send a data message to a given destination.
    * 
    * @param the_destination
    *           Where to send the message.
    * @param the_message
    *           The message to send.
    */
   protected final void sendMessage(final Contact the_destination, final Message the_message) {
      final Map replyMetadata = my_bufferManager.getMetadata(the_message.getMessageID());

      int bufferTimer = ((Integer) replyMetadata.get("Buffer timer")).intValue();
      final long entryTime = ((Long) replyMetadata.get("Entry time")).longValue();
      final long currentTime = System.currentTimeMillis();
      bufferTimer += currentTime - entryTime;

      final StuffedByteArrayOutputStream combinedStream = new StuffedByteArrayOutputStream();
      combinedStream.writeSection(new Integer(bufferTimer).toString().getBytes());
      combinedStream.writeSection(new Long(currentTime).toString().getBytes());
      combinedStream.writeSection(the_message.serialize());

      sendGossipingPDU(the_destination, DATA_HEADER, combinedStream.toByteArray());
   }

   /**
    * Send a message buffer summary to a given destination.
    * 
    * @param the_destination
    *           Where to send the summary.
    * @param the_summary
    *           The summary to send.
    */
   protected final void sendSummary(final Contact the_destination, final Summary the_summary) {
      sendGossipingPDU(the_destination, SUMMARY_HEADER, the_summary.serialize());
   }

   /**
    * Create and send a gossiping PDU with the specified header and data.
    * 
    * @param the_destination
    *           The destination of the PDU.
    * @param the_header
    *           The header to prefix with.
    * @param the_data
    *           The data to send.
    */
   private void sendGossipingPDU(final Contact the_destination, final byte the_header,
         final byte[] the_data) {
      // GRAHAM: allow subclasses access to this method and provide a way to
      // register handlers for given message header bytes: thus they could use
      // this method to send packets with arbitrary header bytes and have a
      // handler which could receive and perform actions based on the packet.
      final byte[] packet = new byte[the_data.length + 1];
      packet[0] = the_header;
      System.arraycopy(the_data, 0, packet, 1, the_data.length);
      my_networkManager.sendMessage(the_destination, packet);
   }

   /**
    * Locate the components necessary for gossiping.
    * 
    * @throws NoSuchComponentException
    *            if an attempt is made to access a component which doesn't
    *            exist.
    */
   public final void setupComponentLinks() throws NoSuchComponentException {
      my_networkManager = (NetworkManager) ComponentRegistry.getComponent(NETWORK_MANAGER);
      my_bufferManager = (BufferManager) ComponentRegistry.getComponent(BUFFER_MANAGER);
      my_membershipManager = (MembershipManager) ComponentRegistry
            .getComponent(MEMBERSHIP_MANAGER);
      my_dataStoreManager = (DataStoreManager) ComponentRegistry
            .getComponent(DATASTORE_MANAGER);
   }

   /**
    * Called when the gossiping thread is about to enter a new round of
    * gossiping. Use this hook for things which must happen on each round.
    */
   protected final void onNextRound() {
      my_bufferManager.ageMessages();
      my_membershipManager.ageContacts();
   }

   /**
    * When the component starts running, start the gossiping thread.
    */
   public final void onRun() {
      my_dataStoreManager.addObserver(this);
      my_gossipThread.start();
      my_messageQueue.scheduleUpdates();
   }

   /**
    * Called when the gossip manager is shutdown. No action needed.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#onShutdown()
    */
   public final void onShutdown() {
      my_dataStoreManager.deleteObserver(this);
      my_messageQueue.cancel();
   }

   /**
    * The thread responsible for initiating gossiping sessions with other nodes.
    * 
    * @author Graham Williamson (graham.williamson@ucd.ie)
    */
   private class GossipThread extends Thread {

      /**
       * The period between each gossiping round.
       */
      private final long my_gossipPeriod;

      /**
       * Create a new gossiping thread with the specified gossip period.
       * 
       * @param a_gossipPeriod
       *           The period between gossip rounds.
       */
      public GossipThread(final long a_gossipPeriod) {
         super();
         my_gossipPeriod = a_gossipPeriod;
      }

      /**
       * The main gossiping loop.
       * 
       * @see java.lang.Runnable#run()
       */
      public final void run() {
         while (!shouldShutdown()) {
            // Wait for the next gossip period to begin
            try {
               Thread.sleep(my_gossipPeriod);
            } catch (InterruptedException e) {
               getLogger().finest("Gossip thread interrupted during sleep.");
            }

            // React to a new round starting
            onNextRound();

            // Choose a target node to gossip with
            final Contact target = my_membershipManager.recommendContact();
            final Summary summary = my_bufferManager.getSummary();

            // Then send the summary
            if (target != null && !summary.isEmpty() && !shouldShutdown()) {
               // getLogger().fine("Gossiping summary to: " + target);
               sendSummary(target, summary);
            }
         }
      }

   }

}
