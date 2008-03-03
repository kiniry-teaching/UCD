//
// $Revision:7373 $: $Date:2008-01-24 11:20:18 +0000 (Thu, 24 Jan 2008) $ - $Author:gstevenson $
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

import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.apache.commons.lang.time.StopWatch;

/**
 * This class attempts to read messages from an input stream. Messages are obtained by calling
 * the getMessage() method.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class MessageReader implements Runnable {

   /**
    * A constant representing 2 min in ms.
    */
   public static final int TWO_MINS_IN_MS = 120000;

   /**
    * A constant representing the integer 100.
    */
   private static final int ONE_HUNDRED = 100;

   /**
    * A constant representing the integer 500.
    */
   private static final int FIVE_HUNDRED = 500;

   /**
    * The message id.
    */
   private String my_messageId;

   /**
    * The length of the message.
    */
   private int my_length;

   /**
    * The payload of the message.
    */
   private String my_payload;

   /**
    * Keep reading from the input stream?
    */
   private boolean my_keepReading;

   /**
    * The input stream associated with this reader.
    */
   private final BufferedInputStream my_inputStream;

   /**
    * A list containing read messages.
    */
   private List my_messageList;

   /**
    * The logger for this class.
    */
   private final Logger my_logger;

   /**
    * Has an error occured?
    */
   private boolean my_errorOccured;

   /**
    * The length of time to wait before reporting a timeout
    */
   private long my_timeout;

   private StopWatch my_stopwatch;

   /**
    * A runnable object that checks the listener for errors and stops the message reader if one
    * has occured.
    */
   private final Runnable my_listenerMonitor = new Runnable() {
      public void run() {
         if (my_errorOccured) {
            try {
               close();
            } catch (IOException e) {
               my_logger.warning("IOException in listener monitor: " + e.getMessage());
            }
         }
      }
   };

   /**
    * An executer service used to schefule checks for errors.
    */
   private final ScheduledExecutorService my_service_scheduler;

   /**
    * Creates a new message reader that will operate over the given InputStream.
    * 
    * @param an_inputStream
    *           the InputStream on which to read messages.
    */
   public MessageReader(final InputStream an_inputStream, ExecutorService an_executorService) {
      my_errorOccured = false;
      my_logger = Logger.getLogger(getClass().getName());
      my_logger.setLevel(Level.WARNING);
      my_inputStream = new BufferedInputStream(an_inputStream);
      my_messageList = new LinkedList();
      my_keepReading = true;
      an_executorService.execute(this);
      my_service_scheduler = Executors.newScheduledThreadPool(1);
      my_service_scheduler.scheduleWithFixedDelay(my_listenerMonitor, 0, FIVE_HUNDRED,
            TimeUnit.MILLISECONDS);
      my_timeout = TWO_MINS_IN_MS;
      my_stopwatch = new StopWatch();
      my_stopwatch.start();
   }

   /**
    * This method will continually attempt to read messages from the message stream and add
    * them to the message list. It will stop reading when the close method is called.
    */
   public void run() {
      while (my_keepReading && !my_errorOccured) {
         try {
            // Read the messageID.
            readMessageId();
            // Next, read the message length.
            readMessageLength();
            // Next, read the message.
            readPayload();
            // Add the new message to the message list
            my_messageList.add(new Message(my_messageId, my_payload));
            my_messageId = null;
            my_length = 0;
            my_payload = null;
            
         } catch (IOException e) {
            my_logger.info("IOException when attempting to read messages: " + e.getMessage());
            my_errorOccured = true;
         } catch (NumberFormatException e) {
            my_logger.warning("IOException when attempting to read messages. "
                  + "Badly formatted message length: " + e.getMessage());
            my_errorOccured = true;
         }
      }
   }

   /**
    * When invoked, this method will attempt to read the specified number of bytes from the
    * input stream. It will block until the required number of bytes are available, or the
    * reader is shutting down
    * 
    * @param the_length
    *           the number of bytes to be read
    * @return a byte[] containing <code>length</code> bytes read from the stream
    * @throws IOException
    *            if an error occurs while reading from the stream.
    */
   private byte[] blockedRead(final int the_length) throws IOException {
      final byte[] byteArray = new byte[the_length];
      int available = 0;
      int currentIndex = 0;
      // While we have not read the entire message
      while (currentIndex != the_length) {
         available = my_inputStream.available();
         // If we can perform a read
         if (available > 0) {
            // Read the minimum of the number of bytes left and the number of bytes available
            my_inputStream.read(byteArray, currentIndex, Math.min(available, the_length
                  - currentIndex));
            // Incrament the current index
            currentIndex += Math.min(available, the_length - currentIndex);
         } else {
            try {
               synchronized (this) {
                  wait(ONE_HUNDRED);
               }
            } catch (InterruptedException e) {
               e.printStackTrace();
            }
         }
         // If we are to terminate
         if (!my_keepReading) {
            throw new IOException("Instructed to stop reading from the message stream");
         }
      }
      return byteArray;

   }

   /**
    * Read the payload from the input stream.
    * 
    * @throws IOException
    *            if an error occurs reading from the stream
    */
   private void readPayload() throws IOException {
      my_payload = new String(blockedRead(my_length));
   }

   /**
    * Read the payload length from the input stream.
    * 
    * @throws IOException
    *            if an error occurs reading from the stream
    * @throws NumberFormatException
    *            if the message length cannot be parsed.
    */
   private void readMessageLength() throws IOException, NumberFormatException {
      my_length = Integer.valueOf(new String(blockedRead(Protocol.PAYLOAD_DESCRIPTOR_SIZE)))
            .intValue();
   }

   /**
    * Read the message id from the input stream.
    * 
    * @throws IOException
    *            if an error occurs reading from the stream
    */
   private void readMessageId() throws IOException {
      my_messageId = new String(blockedRead(Protocol.MESSAGE_ID_LENGTH));
   }

   /**
    * Instructs the class to stop reading from the input stream. This will result in an IO
    * exception being thrown if an exception is raised by the underlying input stream.
    * 
    * @throws IOException
    *            if an error occurs closing the underlying input stream.
    */
   public void close() throws IOException {
      my_keepReading = false;
      my_service_scheduler.shutdown();
      my_inputStream.close();
   }

   /**
    * Are messages available?
    * 
    * @return true if messages are available, false otherwise.
    */
   public boolean available() {
      return my_messageList.size() != 0;
   }

   /**
    * Returns the next message available. Will block if no messages are avaialable.
    * 
    * @return the next message available.
    * @throws InterruptedException
    *            if the message reader is instructed to close.
    */
   public Message getMessage() throws InterruptedException, TimeoutException {
      while (!available()) {
         synchronized (this) {
            wait(ONE_HUNDRED);
         }
         if (!my_keepReading) {
            throw new InterruptedException("MessageReader instructed to close");
         }
         // System.err.println(this + " - " + (my_timeout - splitTime));
         if (hasTimedOut()) {
            my_errorOccured = true;
            throw new TimeoutException("Socket Timeout Occured (" + my_timeout + ")");
         }
      }
      // Remove the message at the head of the list and return
      final Message message = (Message) my_messageList.get(0);
      my_messageList.remove(0);
      my_stopwatch.stop();
      my_stopwatch.reset();
      my_stopwatch.start();
      return message;
   }

   /**
    * Whether this message reader has timed out.
    * 
    * @return true if it has timed out, false otherwise.
    */
   public boolean hasTimedOut() {
      my_stopwatch.split();
      long splitTime = my_stopwatch.getSplitTime();
      my_stopwatch.unsplit();
      return splitTime > my_timeout;
   }

}
