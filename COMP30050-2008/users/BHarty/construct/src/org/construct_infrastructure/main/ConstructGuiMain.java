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
package org.construct_infrastructure.main;

import org.construct_infrastructure.gui.ConstructGUI;

/**
 * Utility class that runs the Construct GUI. 
 * @author Lorcan Coyle (lorcan.coyle@ucd.ie)
 *
 */
public final class ConstructGuiMain {

   /**
    * Empty hidden constructor.
    *
    */
   private ConstructGuiMain() {
   };

   /**
    * Runs the Construct GUI.
    * @param the_args the arguments passed to the main method. These are not used.
    */
   public static void main(final String[] the_args) {
      final ConstructGUI inst = new ConstructGUI();
      inst.setLocationByPlatform(true);
      inst.setVisible(true);
   }

}
