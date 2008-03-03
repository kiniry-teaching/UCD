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
package org.construct_infrastructure.component.gossiping.util;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;

/**
 * This class represents a stream of bytes which are byte stuffed using the PPP
 * specification. It is possible to add different sections to the stream by
 * calling markSection() - this inserts a separator byte, allowing the stream to
 * be split into the original sections later.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 * @author Steve Neely (steve.neely@ucd.ie)
 */
public class StuffedByteArrayOutputStream extends OutputStream {

   /**
    * The separator sequence between data and my_metadata segments in a data
    * summary is ~ or 0x7E in ASCII.
    */
   private static final byte SEP_BYTE = 0x7E;

   /**
    * The control escape byte used to pad data.
    */
   private static final byte CTRL_ESC_BYTE = 0x7D;

   /**
    * During a stuff operation, everywhere that Ox7D (CTRL_ESC_BYTE) appears in
    * the data it is replaced with the two-character sequence Ox7D,Ox5D. This
    * constant represents the STUFFER byte 0x5D.
    */
   private static final byte CTRL_ESC_BYTE_STUFFER = 0x5D;

   /**
    * During a stuff operation, everywhere that 0x7E appears in the data it is
    * replaced with the two character sequence Ox7D,Ox5E. This constant
    * represents the STUFFER byte 0x5E.
    */
   private static final byte SEP_BYTE_STUFFER = 0x5E;

   /**
    * The underlying output stream which we stuff bytes into.
    */
   private final ByteArrayOutputStream my_buffer;

   /**
    * Create a new, empty, stuff byte array output stream.
    */
   public StuffedByteArrayOutputStream() {
      super();
      my_buffer = new ByteArrayOutputStream();
   }

   /**
    * Write a section to the stream which can later be recovered.
    * 
    * @param some_bytes
    *           The bytes to write.
    */
   public final void writeSection(final byte[] some_bytes) {
      for (int i = 0; i < some_bytes.length; i++) {
         write(some_bytes[i]);
      }
      markSection();
   }

   /**
    * Write a byte to the stream.
    * 
    * @see java.io.OutputStream#write(int)
    * @param a_byte
    *           The byte to be written.
    */
   public final void write(final int a_byte) {
      if (a_byte == CTRL_ESC_BYTE) {
         my_buffer.write(CTRL_ESC_BYTE);
         my_buffer.write(CTRL_ESC_BYTE_STUFFER);
      } else if (a_byte == SEP_BYTE) {
         my_buffer.write(CTRL_ESC_BYTE);
         my_buffer.write(SEP_BYTE_STUFFER);
      } else {
         my_buffer.write(a_byte);
      }
   }

   /**
    * Mark the end of a section in the stuffed stream so that the section can
    * later be recovered.
    */
   public final void markSection() {
      my_buffer.write(SEP_BYTE);
   }

   /**
    * Get this buffer as a byte array.
    * 
    * @return The contents of this buffer as a byte array.
    */
   public final byte[] toByteArray() {
      return my_buffer.toByteArray();
   }

}
