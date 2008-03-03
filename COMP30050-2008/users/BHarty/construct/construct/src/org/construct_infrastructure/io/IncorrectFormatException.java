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
package org.construct_infrastructure.io;

/**
 * This class is used to represent errors that occur in the trasmission of messages between
 * components and entities.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public class IncorrectFormatException extends Exception {

   /**
    * Serial version ID.
    */
   private static final long serialVersionUID = 1L;

   /**
    * Creates a new IncorrectFormatException with the given error message.
    * 
    * @param a_message
    *           the message describing the error which caused the exception.
    */
   public IncorrectFormatException(final String a_message) {
      super(a_message);
   }

   /**
    * Creates a new IncorrectFormatException with the given error message.
    * 
    * @param a_message
    *           the message describing the error which caused the exception.
    * @param a_cause
    *           the cause of this exception being generated.
    */
   public IncorrectFormatException(final String a_message, final Throwable a_cause) {
      super(a_message, a_cause);
   }
}
