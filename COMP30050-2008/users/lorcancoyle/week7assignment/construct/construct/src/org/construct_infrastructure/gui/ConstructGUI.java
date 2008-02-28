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
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;

import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextPane;
import javax.swing.WindowConstants;

import org.construct_infrastructure.loader.ComponentCreationException;
import org.construct_infrastructure.loader.ComponentLoader;
import org.construct_infrastructure.loader.PropertyFileException;
import org.construct_infrastructure.loader.StringLogDisplay;

/**
 * This code was edited or generated using CloudGarden's Jigloo SWT/Swing GUI Builder, which is
 * free for non-commercial use. If Jigloo is being used commercially (ie, by a corporation,
 * company or business for any purpose whatever) then you should purchase a license for each
 * developer using Jigloo. Please visit www.cloudgarden.com for details. Use of Jigloo implies
 * acceptance of these licensing terms. A COMMERCIAL LICENSE HAS NOT BEEN PURCHASED FOR THIS
 * MACHINE, SO JIGLOO OR THIS CODE CANNOT BE USED LEGALLY FOR ANY CORPORATE OR COMMERCIAL
 * PURPOSE.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public class ConstructGUI extends javax.swing.JFrame implements StringLogDisplay {

   {
      // Set Look & Feel
      try {
         javax.swing.UIManager
               .setLookAndFeel("com.jgoodies.looks.plastic.Plastic3DLookAndFeel");
      } catch (Exception e) {
         e.printStackTrace();
      }
   }

   private static final long serialVersionUID = 1L;

   private JButton my_stopButton;

   private JTabbedPane tabContainer;

   private JTextPane my_logTextArea;

   private JPanel buttonPanel;

   private JButton aboutButton;

   private JButton my_exitButton;

   private JScrollPane textScrollPane;

   private JButton my_startButton;

   /**
    * The instance of construct associated with this GUI.
    */
   private ComponentLoader my_construct;

   public ConstructGUI() {
      super();
      initGUI();
   }

   /**
    * Adds a new tab to the gui.
    * 
    * @param a_tabName
    *           The name of the tab to display.
    * @param a_tab
    *           The panel to display in the new tab.
    */
   public final void addTab(final String a_tabName, final JPanel a_tab) {
      tabContainer.addTab(a_tabName, null, a_tab, null);
   }

   /**
    * Removes all tabs from the gui.
    */
   public final void removeTabs() {
      tabContainer.removeAll();
      tabContainer.addTab("Log", null, textScrollPane, null);
   }

   private void initGUI() {
      try {
         BorderLayout thisLayout = new BorderLayout();
         getContentPane().setLayout(thisLayout);
         setTitle("Construct");
         getContentPane().setBackground(new java.awt.Color(255, 255, 255));
         String resourcePrefix = "ie/ucd/srg/construct/gui/";
         setIconImage(new ImageIcon(getClass().getClassLoader().getResource(
               resourcePrefix + "asterisk_orange.png")).getImage());
         setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
         {
            tabContainer = new JTabbedPane();
            getContentPane().add(tabContainer, BorderLayout.CENTER);
            tabContainer.setBackground(new java.awt.Color(0, 0, 0));
            {
               textScrollPane = new JScrollPane();
               tabContainer.addTab("Log", null, textScrollPane, null);
               textScrollPane.setToolTipText("Construct Log");
               textScrollPane.setBackground(new java.awt.Color(192, 192, 192));
               {
                  my_logTextArea = new JTextPane();
                  textScrollPane.setViewportView(my_logTextArea);
                  my_logTextArea.setEditable(false);
               }
            }
         }
         {
            buttonPanel = new JPanel();
            getContentPane().add(buttonPanel, BorderLayout.SOUTH);
            buttonPanel.setBackground(new java.awt.Color(255, 255, 255));
            {
               my_startButton = new JButton();
               buttonPanel.add(my_startButton);
               my_startButton.setText("Start");
               my_startButton.setToolTipText("Start Construct");
               my_startButton.setIcon(new ImageIcon(getClass().getClassLoader().getResource(
                     resourcePrefix + "control_play_blue.png")));
               my_startButton.addMouseListener(new MouseAdapter() {
                  public void mouseClicked(MouseEvent an_evt) {
                     startButtonMouseClicked(an_evt);
                  }
               });
            }
            {
               my_stopButton = new JButton();
               buttonPanel.add(my_stopButton);
               my_stopButton.setText("Stop");
               my_stopButton.setToolTipText("Stop Construct");
               my_stopButton.setEnabled(false);
               my_stopButton.setIcon(new ImageIcon(getClass().getClassLoader().getResource(
                     resourcePrefix + "control_stop_blue.png")));
               my_stopButton.addMouseListener(new MouseAdapter() {
                  public void mouseClicked(final MouseEvent an_evt) {
                     stopButtonMouseClicked(an_evt);
                  }
               });
            }
            {
               my_exitButton = new JButton();
               buttonPanel.add(my_exitButton);
               my_exitButton.setText("Exit");
               my_exitButton.setToolTipText("Exit");
               my_exitButton.setIcon(new ImageIcon(getClass().getClassLoader().getResource(
                     resourcePrefix + "cross.png")));
               my_exitButton.addMouseListener(new MouseAdapter() {
                  public void mouseClicked(final MouseEvent an_evt) {
                     exitButtonMouseClicked(an_evt);
                  }
               });
            }
            {
               aboutButton = new JButton();
               buttonPanel.add(aboutButton);
               aboutButton.setText("About");
               aboutButton.setIcon(new ImageIcon(getClass().getClassLoader().getResource(
                     resourcePrefix + "information.png")));
               aboutButton.addMouseListener(new MouseAdapter() {
                  public void mouseClicked(final MouseEvent an_evt) {
                     aboutButtonMouseClicked(an_evt);
                  }
               });
            }
         }
         setSize(519, 308);
      } catch (Exception e) {
         e.printStackTrace();
      }
   }

   private void startButtonMouseClicked(MouseEvent evt) {
      if (my_startButton.isEnabled()) {
         my_startButton.setEnabled(false);
         my_exitButton.setEnabled(false);
         try {
            my_construct = new ComponentLoader(this, new File("construct.properties"));
            // load the ontologies
            // OntologyLoader.ontologies();
            // new Thread(construct).start();
            my_stopButton.setEnabled(true);
         } catch (ComponentCreationException e) {
            log(e.getMessage());
            my_startButton.setEnabled(true);
            my_exitButton.setEnabled(true);
         } catch (PropertyFileException e) {
            log(e.getMessage());
            log("\nThe construct.properties file was not found. A sample property file ");
            log("was packaged with the Construct distribution. Please use that file ");
            log("as a basis for your own configuration files.\n");
            my_startButton.setEnabled(true);
            my_exitButton.setEnabled(true);
         }
      }
   }

   private void stopButtonMouseClicked(MouseEvent evt) {
      if (my_stopButton.isEnabled()) {
         my_stopButton.setEnabled(false);
         my_construct.shutdown();
         my_startButton.setEnabled(true);
         my_exitButton.setEnabled(true);
      }
   }

   private void exitButtonMouseClicked(MouseEvent evt) {
      if (my_exitButton.isEnabled()) {
         my_exitButton.setEnabled(false);
         my_startButton.setEnabled(false);
         my_stopButton.setEnabled(false);
         my_logTextArea.setText(my_logTextArea.getText() + "\nExiting...");
         dispose();
         System.exit(0);
      }
   }

   public void forceShutdown() {
      my_startButton.setEnabled(false);
      my_exitButton.setEnabled(false);
      my_stopButton.setEnabled(false);
      if (my_construct != null) {
         my_construct.shutdown();
      }

   }

   /**
    * Adds a message to the log text area.
    * 
    * @param a_message
    *           The message to be logged.
    */
   public final void log(final String a_message) {
      my_logTextArea.setText(my_logTextArea.getText() + "\n" + a_message);
      // Set caret at the end of the log
      my_logTextArea.setCaretPosition(my_logTextArea.getDocument().getLength());
   }

   private void aboutButtonMouseClicked(MouseEvent evt) {
      AboutDialog about = new AboutDialog(this);
      about.setLocationRelativeTo(this);
      about.setVisible(true);
      // TODO add your code for aboutButton.mouseClicked
   }

}
