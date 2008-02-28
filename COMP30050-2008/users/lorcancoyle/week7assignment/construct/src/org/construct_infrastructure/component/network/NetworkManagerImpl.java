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
package org.construct_infrastructure.component.network;


import java.io.IOException;
import java.net.DatagramPacket;
import java.net.DatagramSocket;
import java.net.SocketException;
import java.util.Properties;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.component.gossiping.GossipManager;
import org.construct_infrastructure.component.gossiping.membership.Contact;
import org.construct_infrastructure.component.gossiping.membership.MembershipManager;
import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;

import com.apple.dnssd.BrowseListener;
import com.apple.dnssd.DNSSD;
import com.apple.dnssd.DNSSDException;
import com.apple.dnssd.DNSSDRegistration;
import com.apple.dnssd.DNSSDService;
import com.apple.dnssd.RegisterListener;

/**
 * This class uses the bonjour protocol to form the network layer of construct.
 * One limitation which needs to be addressed is that default packet sizes are
 * set to 20480 bytes. It is likely that we will need to gossip summaries which
 * exceed this size.
 * 
 * We also assume that there is a single construct deployment per IP address
 * (resolving IP to nodeID). This may always be the case, but is something to
 * think about.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public class NetworkManagerImpl extends AbstractConstructComponent implements NetworkManager,
      RegisterListener, BrowseListener, BonjourContactResolvedListener {

   /**
    * The interface for the gossip manager.
    */
   public static final String GOSSIP_MANAGER
      = "org.construct_infrastructure.component.gossiping.GossipManager";

   /**
    * The interface for the membership manager.
    */
   public static final String MEMBERSHIP_MANAGER
      = "org.construct_infrastructure.component.gossiping.membership.MembershipManager";

   /**
    * The construct registration string.
    */
   public static final String BONJOUR_REGISTRATION_TYPE = "_construct_gossip._udp";

   /**
    * Bit mask for the lower 16 bits.
    */
   private static final int BIT_MASK_16 = 0xFFFF;

   /**
    * Bit mask for the lower 8 bits.
    */
   private static final int BIT_MASK_8 = 0xFF;
   
   /**
    * The packet size for comms.
    */
   private static final int PACKET_SIZE = 60000;

   /**
    * The number of bytes overhead added to packets by the network manager.
    */
   private static final int NETWORK_OVERHEAD = 2;

   /**
    * The Gossip Manager which the network layer sends received data to.
    */
   private GossipManager my_gossipManager;

   /**
    * The membership manager to notify when nodes join or leave the network.
    */
   private MembershipManager my_membershipManager;

   /**
    * Used to identify the local node.
    */
   private String my_localNodeID;

   /**
    * The local port which the network manager listens for incoming data on.
    */
   private final int my_inboundPort;

   /**
    * The socket that the network manager listens for incoming data on.
    */
   private final DatagramSocket my_inboundSocket;

   /**
    * The data packet which the network manager reads into.
    */
   private final DatagramPacket my_inboundDataPacket;

   /**
    * The outbound data socket.
    */
   private final DatagramSocket my_outboundSocket;

   /**
    * The bonjour registration for this node.
    */
   private DNSSDRegistration my_registration;

   /**
    * The bonjour service browser.
    */
   private DNSSDService my_browser;

   /**
    * The constructor creates a new network manager, and registers itself using
    * bonjour.
    * 
    * @param some_properties
    *           The properties for this component.
    * 
    * @throws SocketException
    *            if the inbound or outbound sockets cannot be created
    * @throws DNSSDException
    *            if an error occurs registering the object.
    */
   public NetworkManagerImpl(final Properties some_properties) throws SocketException,
         DNSSDException {
      super();
      setProperties(some_properties);

      // Setup the socket connections
      my_inboundSocket = new DatagramSocket();
      my_inboundPort = my_inboundSocket.getLocalPort();
      my_inboundDataPacket = new DatagramPacket(new byte[PACKET_SIZE], PACKET_SIZE);
      my_outboundSocket = new DatagramSocket();

      // Setup local node identity
      my_localNodeID = "CONSTRUCT[" + System.getProperty("user.name") + "]";
   }

   /**
    * Locate the gossip manager and membership manager.
    * 
    * @throws NoSuchComponentException
    *            if an attempt is made to access a component which doesnt exist.
    */
   public final void setupComponentLinks() throws NoSuchComponentException {
      my_gossipManager = (GossipManager) ComponentRegistry.getComponent(GOSSIP_MANAGER);
      my_membershipManager = (MembershipManager) ComponentRegistry
            .getComponent(MEMBERSHIP_MANAGER);
   }

   /**
    * Register with bonjour and start the listening thread.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#onRun()
    */
   public final void onRun() {
      // Register as a bonjour service
      try {
         my_registration = DNSSD.register(0, 0, my_localNodeID, BONJOUR_REGISTRATION_TYPE, "",
               "", my_inboundPort, null, this);
      } catch (DNSSDException e) {
         getLogger().severe(
               "Error while attempting to register network layer gossiping service.");
      }
      // Create a Thread to listen for incoming gossips
      new ListenerThread(my_inboundSocket, my_inboundDataPacket).start();
   }

   /**
    * Called when the component is shutdown.
    * 
    * @see org.construct_infrastructure.component.AbstractConstructComponent#onShutdown()
    */
   public final void onShutdown() {
      if (my_registration != null) { 
         my_registration.stop();
      }
      if (my_browser != null) {
         my_browser.stop();
      }
      if (my_inboundSocket != null) {
         my_inboundSocket.close();
      }
   }

   /**
    * This method is invoked by callback once registered as a bonjour service.
    * When this occurs we need to check if our localID has been changed due to
    * collisions and then browse for other construct deployments.
    * 
    * @see com.apple.dnssd.RegisterListener#serviceRegistered(
    *      com.apple.dnssd.DNSSDRegistration, int, java.lang.String,
    *      java.lang.String, java.lang.String)
    * 
    * @param a_registration
    *           The active registration.
    * @param the_flags
    *           Unused.
    * @param a_serviceName
    *           The service name registered.
    * @param the_regType
    *           The type of service registered.
    * @param the_domain
    *           The domain it was registered on.
    */
   public final void serviceRegistered(final DNSSDRegistration a_registration,
         final int the_flags, final String a_serviceName, final String the_regType,
         final String the_domain) {
      // Our name may have been renamed on collision
      my_localNodeID = a_serviceName;
      // We're registered now start browsing...
      try {
         my_browser = DNSSD.browse(0, 0, BONJOUR_REGISTRATION_TYPE, "", this);
      } catch (DNSSDException e) {
         // GRAHAM: We need to do something better here. Is there a way to
         // shutdown construct with an error message for the user?
         getLogger().severe("Unable to browse the network!");
      }
   }

   /**
    * Called if an error occurs during service registration or the browse
    * request.
    * 
    * @param a_service
    *           the service invoking the callback.
    * @param an_errorCode
    *           the code representing the error that occured.
    */
   public final void operationFailed(final DNSSDService a_service, final int an_errorCode) {
      // GRAHAM: This is a problem if the registration fails; not so much
      // if a browse fails (I think!). Separate them and...do we need to stop
      // construct if we can't register?
      getLogger().severe(
            "Service reported error during registration of browsing of the network: Error #"
                  + String.valueOf(an_errorCode));
   }

   /**
    * The Browser invokes this callback when a service is discovered. If this
    * service is not already known to us (and is not us) we will add it to the
    * contact list.
    * 
    * @param a_browser
    *           The active browse service.
    * @param the_flags
    *           Any flags: e.g. DNSSD.MORE_COMING.
    * @param an_ifIndex
    *           The interface the service was discovered on.
    * @param a_serviceName
    *           The services name.
    * @param a_regType
    *           The type of service.
    * @param a_domain
    *           The domain of the service.
    */

   public final void serviceFound(final DNSSDService a_browser, final int the_flags,
         final int an_ifIndex, final String a_serviceName, final String a_regType,
         final String a_domain) {
      if (!my_localNodeID.equals(a_serviceName)) {
         getLogger().fine("Service discovered: " + a_serviceName);
         final BonjourContact contact = new BonjourContact(a_serviceName, a_domain, a_regType,
               an_ifIndex);
         try {
            contact.resolve(this);
         } catch (DNSSDException e) {
            getLogger().warning("Unable to resolve contact: " + a_serviceName);
         }
      }
   }

   /**
    * The Browser invokes this callback when a service is lost. If this service
    * is known to us we will remove it from the contact list.
    * 
    * @param a_browser
    *           The active browse service.
    * @param the_flags
    *           Any flags: e.g. DNSSD.MORE_COMING.
    * @param an_ifIndex
    *           The interface the service was discovered on.
    * @param a_serviceName
    *           The services name.
    * @param a_regType
    *           The type of service.
    * @param a_domain
    *           The domain of the service.
    */
   public final void serviceLost(final DNSSDService a_browser, final int the_flags,
         final int an_ifIndex, final String a_serviceName, final String a_regType,
         final String a_domain) {
      getLogger().fine("Service lost: " + a_serviceName);
      my_membershipManager.contactLost(new BonjourContact(a_serviceName, a_domain, a_regType,
            an_ifIndex));
   }

   /**
    * Callback to notify when a contact has been resolved.
    * 
    * @see org.construct_infrastructure.component.network.BonjourContactResolvedListener#
    *      contactResolved(org.construct_infrastructure.component.network.BonjourContact)
    * @param the_contact
    *           The contact that was resolved.
    */
   public final void contactResolved(final BonjourContact the_contact) {
      my_membershipManager.contactDiscovered(the_contact);
   }

   /**
    * Callback to notify when an error occurred during the resolve and the
    * contact was not able to be fully resolved.
    * 
    * @see org.construct_infrastructure.component.network.BonjourContactResolvedListener#resolveFailed(
    *      org.construct_infrastructure.component.network.BonjourContact,
    *      java.lang.String)
    * @param the_contact
    *           The contact which failed to resolve.
    * @param a_message
    *           A message detailing the error.
    */
   public final void resolveFailed(final BonjourContact the_contact, final String a_message) {
      getLogger().warning(a_message);
   }

   /**
    * Send a message to a particular contact.
    * 
    * @see org.construct_infrastructure.component.network.NetworkManager#sendMessage(
    *      org.construct_infrastructure.component.gossiping.membership.Contact, byte[])
    * @param a_contact
    *           The contact to send to.
    * @param some_data
    *           The data to send.
    */
   public final void sendMessage(final Contact a_contact, final byte[] some_data) {
      // Make sure the contact has an IP address
      if (!(a_contact instanceof IPContact)) {
         getLogger().fine("Unknown contact type. Unable to gossip with " + a_contact);
         return;
      }

      // Add the network layer overhead (this is just the reply-to port)
      final byte[] packet = new byte[some_data.length + NETWORK_OVERHEAD];
      packet[0] = (byte) (((my_inboundPort & BIT_MASK_16) >> Byte.SIZE) & BIT_MASK_8);
      packet[1] = (byte) ((my_inboundPort) & BIT_MASK_8);
      System.arraycopy(some_data, 0, packet, NETWORK_OVERHEAD, some_data.length);

      // Then send the datagram
      final IPContact target = (IPContact) a_contact;
//      getLogger().fine("Sending " + packet.length + " bytes to " + target);
      try {
         my_outboundSocket.send(new DatagramPacket(packet, packet.length, target.getAddress(),
               target.getPort()));
      } catch (IOException e) {
         getLogger().warning("Error sending datagram. Unable to gossip with " + target);
      }
   }

   /**
    * The ListenerThread waits on a message arriving and passes it up the stack
    * to the gossip manager.
    * 
    * @author Graham Williamson (graham.williamson@ucd.ie)
    * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
    */
   private class ListenerThread extends Thread {
      /**
       * The socket to be monitored by this listener.
       */
      private final DatagramSocket my_socket;

      /**
       * The packet to be filled with received data.
       */
      private final DatagramPacket my_packet;

      /**
       * Creates a new listener thread for a given network manager.
       * 
       * @param a_socket
       *           the socket to be monitored by this listener.
       * @param a_packet
       *           the packet to be filled with received data.
       */
      public ListenerThread(final DatagramSocket a_socket, final DatagramPacket a_packet) {
         super();
         my_socket = a_socket;
         my_packet = a_packet;
      }

      /**
       * The run method monitors the socket for incoming data, receives it, and
       * then passes it up the stack to the gossip manager.
       */
      public void run() {
         Contact from;
         int replyPort;
         Contact replyTo;

         while (!shouldShutdown() && !my_socket.isClosed()) {
            try {
               my_socket.receive(my_packet);
               final byte[] packetData = my_packet.getData();
               final int packetOffset = my_packet.getOffset();

               // Build the from and reply-to contacts
               from = new BasicIPContact(my_packet.getAddress(), my_packet.getPort());
               replyPort = ((packetData[packetOffset] & BIT_MASK_8) << Byte.SIZE)
                     | (packetData[packetOffset + 1] & BIT_MASK_8);
               replyTo = new BasicIPContact(my_packet.getAddress(), replyPort);

//               getLogger().fine(
//                     "Message from: " + from + " (" + my_packet.getLength()
//                           + " bytes), reply to: " + replyTo);

               // Copy out the recieved data
               final int dataLength = my_packet.getLength() - NETWORK_OVERHEAD;
               final byte[] received = new byte[dataLength];
               System.arraycopy(my_packet.getData(), my_packet.getOffset() + NETWORK_OVERHEAD,
                     received, 0, dataLength);

               // Pass to the gossip manager
               my_gossipManager.receivedGossip(from, replyTo, received);
            } catch (IOException e) {
               getLogger().warning("IO error while listening for gossiped data.");
            }
         }
      }

   }

}
