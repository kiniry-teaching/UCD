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

import java.util.zip.DataFormatException;
import java.util.zip.Deflater;
import java.util.zip.Inflater;

/**
 * This class contains a number of useful utilities for transforming and
 * manipulating various RDF storage structures such as: Jena Models, UTF-8
 * triples, DOM trees and byte[] representations of RDF.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 */
public final class DataTransformer {

   /**
    * Buffer size in bytes.
    */
   private static final int BUFF_SIZE = 1024;

   /**
    * This class cannot be instatiated.
    */
   private DataTransformer() {
      super();
   }

   /**
    * Method that takes an array of bytes and compresses them using ZLIB.
    * 
    * @param the_data
    *           the bytes to be compressed
    * @return an array of ZLIB compressed bytes
    * 
    * @throws TransformationException
    *            will be thrown if the compression fails
    */
   public static byte[] compressBytes(final byte[] the_data) throws TransformationException {
      int compressedByteCount = 0;

      // Create a compressor, working at max compression level and give it the
      // data to compress
      final Deflater compressor = new Deflater();
      compressor.setLevel(Deflater.BEST_COMPRESSION);
      compressor.setInput(the_data);
      compressor.finish();

      // Create a stream to compress the bytes into. We cannot use a static
      // sized array because there is no gaurantee that the compressed version
      // will be smaller than the original uncompressed data
      final ByteArrayOutputStream bos = new ByteArrayOutputStream(the_data.length);

      // Compress data up to 1k at a time
      final byte[] compressedBytesBuffer = new byte[BUFF_SIZE];
      while (!compressor.finished()) {
         final int bytesCompressed = compressor.deflate(compressedBytesBuffer);
         bos.write(compressedBytesBuffer, 0, bytesCompressed);
         compressedByteCount += bytesCompressed;
      }

      // Note: we don't close the ByteArrayOutputStream (it does nothing)
      return bos.toByteArray();
   }

   /**
    * Method that takes an array of bytes and decompresses them.
    * 
    * @param the_data
    *           the byte[] to decompress
    * @return the decompressed data
    * 
    * @throws TransformationException
    *            thrown if the decompression fails. Most likely the data format
    *            is incorrect - not ZLib compressed.
    */
   public static byte[] decompressBytes(final byte[] the_data) throws TransformationException {

      // Create decompressor and give it data to decompress
      final Inflater decompressor = new Inflater();
      decompressor.setInput(the_data);

      // Create expandable byte array to hold decomrpessed data
      final ByteArrayOutputStream bos = new ByteArrayOutputStream(the_data.length);

      // Decompress 1k at a time
      final byte[] decompressedBytesBuffer = new byte[BUFF_SIZE];
      while (!decompressor.finished()) {
         try {
            final int bytesDecompressed = decompressor.inflate(decompressedBytesBuffer);
            bos.write(decompressedBytesBuffer, 0, bytesDecompressed);
         } catch (DataFormatException dfe) {
            throw new TransformationException("Decompression failure. Data format incorrect:",
                  dfe);
         }
      }

      // Note: we don't close the ByteArrayOutputStream (it does nothing)
      return bos.toByteArray();
   }

}
