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
package org.construct_infrastructure.gui;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import javax.swing.JButton;

import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JTextPane;
import javax.swing.WindowConstants;

/**
 * This code was edited or generated using CloudGarden's Jigloo SWT/Swing GUI Builder, which is
 * free for non-commercial use. If Jigloo is being used commercially (ie, by a corporation,
 * company or business for any purpose whatever) then you should purchase a license for each
 * developer using Jigloo. Please visit www.cloudgarden.com for details. Use of Jigloo implies
 * acceptance of these licensing terms. A COMMERCIAL LICENSE HAS NOT BEEN PURCHASED FOR THIS
 * MACHINE, SO JIGLOO OR THIS CODE CANNOT BE USED LEGALLY FOR ANY CORPORATE OR COMMERCIAL
 * PURPOSE.
 */
public class AboutDialog extends javax.swing.JDialog {
   
   private static final long serialVersionUID = 1L;
   
   private JTextPane jTextPane1;

   private JPanel buttonPanel;

   private JButton okButton;

   {
      // Set Look & Feel
      try {
         javax.swing.UIManager
               .setLookAndFeel("com.jgoodies.looks.plastic.Plastic3DLookAndFeel");
      } catch (Exception e) {
         e.printStackTrace();
      }
   }

   public AboutDialog(JFrame frame) {
      super(frame);
      initGUI();
   }

   private void initGUI() {
      try {
         {
            jTextPane1 = new JTextPane();
            this.setTitle("About Construct");
            this.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            getContentPane().add(jTextPane1, BorderLayout.CENTER);
            jTextPane1.setText("Construct, a context-aware systems platform.\n"
                  + "Copyright (c) 2006, 2007 UCD Dublin. All rights reserved.\n\n"
                  + "Construct is free software; you can redistribute it and/or modify"
                  + "it under the terms of the GNU Lesser General Public License as"
                  + "published by the Free Software Foundation; either version 2.1 of"
                  + "the License, or (at your option) any later version.\n\n"
                  + "See http://construct-infrastructure.org for details.\n\n"
                  + "This product includes software developed by the\n"
                  + "Apache Software Foundation (http://www.apache.org/).");
            jTextPane1.setEditable(false);
         }
         {
            buttonPanel = new JPanel();
            FlowLayout buttonPanelLayout = new FlowLayout();
            getContentPane().add(buttonPanel, BorderLayout.SOUTH);
            buttonPanel.setLayout(buttonPanelLayout);
            buttonPanel.setBackground(new java.awt.Color(255, 255, 255));
            {
               okButton = new JButton();
               buttonPanel.add(okButton);
               okButton.setText("OK");
               okButton.addMouseListener(new MouseAdapter() {
                  public void mouseClicked(MouseEvent evt) {
                     okButtonMouseClicked(evt);
                  }
               });
            }
         }
         this.setSize(300, 260);
      } catch (Exception e) {
         e.printStackTrace();
      }
   }

   private void okButtonMouseClicked(MouseEvent evt) {
      this.dispose();
   }

}
