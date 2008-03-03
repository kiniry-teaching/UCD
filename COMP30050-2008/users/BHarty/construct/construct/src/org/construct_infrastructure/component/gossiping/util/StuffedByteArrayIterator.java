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
import java.io.IOException;

/**
 * Splits a stuffed byte array into the original unstuffed constituent sections.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class StuffedByteArrayIterator {

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
    * Mask byte that we will XOR with.
    */
   private static final byte MASK = 0x20;

   /**
    * Copy of the array we are splitting.
    */
   private final byte[] my_array;

   /**
    * The current index into the array.
    */
   private int my_currentIndex;

   /**
    * Create new stuffed byte array iterator which will split the given array
    * into the constituent, unstuffed, sections.
    * 
    * @param the_array
    *           The array to split.
    */
   public StuffedByteArrayIterator(final byte[] the_array) {
      super();
      my_array = (byte[]) the_array.clone();
      my_currentIndex = 0;
   }

   /**
    * Determine whether there is another section available.
    * 
    * @return Whether there is another section.
    */
   public final boolean hasAnotherSection() {
      return my_currentIndex < my_array.length;
   }

   /**
    * Get the next section from the stream.
    * 
    * @return The next section.
    * @throws IOException
    *            If there are no more sections.
    */
   public final byte[] nextSection() throws IOException {
      final ByteArrayOutputStream unstuffed = new ByteArrayOutputStream();

      // Make sure there's another section
      if (!hasAnotherSection()) {
         throw new IOException("No more sections!");
      }

      // Scroll through the array until we reach either the end or the SEP_BYTE,
      // unstuffing as we go
      while (my_currentIndex < my_array.length && my_array[my_currentIndex] != SEP_BYTE) {
         if (my_array[my_currentIndex] == CTRL_ESC_BYTE
               && my_currentIndex + 1 < my_array.length) {
            unstuffed.write(my_array[my_currentIndex + 1] ^ MASK);
            ++my_currentIndex;
         } else {
            unstuffed.write(my_array[my_currentIndex]);
         }
         ++my_currentIndex;
      }

      // Skip past the separator byte
      my_currentIndex++;

      // Return the sub-section
      return unstuffed.toByteArray();
   }
}
