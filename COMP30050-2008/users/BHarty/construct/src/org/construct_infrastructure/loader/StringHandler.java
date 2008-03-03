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
package org.construct_infrastructure.loader;

import java.util.Date;
import java.util.logging.Handler;
import java.util.logging.LogRecord;

/**
 * Handler class for a logger. Outputs messages to classes wich accept logged input as a string
 * (by implementing the StringLogger interface).
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public class StringHandler extends Handler {

   /**
    * Reference to the class which implements the StringLogger interface, which this class will
    * pass log messages to.
    */
   private final StringLogDisplay my_logPanel;

   /**
    * Creates a new handler and associates it with a given target.
    * 
    * @param a_logPanel
    *           the target for all the log messages.
    */
   public StringHandler(final StringLogDisplay a_logPanel) {
      super();
      my_logPanel = a_logPanel;
   }

   /**
    * Not used.
    */
   public void close() {
      // Not required
   }

   /**
    * Not used.
    */
   public void flush() {
      // Not required
   }

   /**
    * Formats and passes the log messages to the associated display class.
    * 
    * @param a_record
    *           The logRecord object which provides the data to be formatted and displayed.
    */
   public final void publish(final LogRecord a_record) {
      // first see if this entry should be filtered out
      // the filter should keep anything
      if (getFilter() != null && !getFilter().isLoggable(a_record)) {
         return;
      }
      my_logPanel.log(new Date(a_record.getMillis()) + ": " + a_record.getSourceClassName()
            + ":" + a_record.getSourceMethodName() + "()");
      my_logPanel.log(a_record.getLevel().getName() + ": " + a_record.getMessage());
   }
}
