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
package org.construct_infrastructure.component.datastorage.viewer;


import javax.swing.JButton;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.table.TableModel;

import org.construct_infrastructure.component.datastorage.DataStoreManager;

/**
 * A simple graphical display of a data store in a table.
 * 
 * @author Graham Williamson (graham.williamson@ucd.ie)
 */
public class ViewerPanel extends JPanel {

   /**
    * A SPARQL query which returns all the data currently in the datastore.
    */
   public static final String QUERY_ALL_DATA
      = "SELECT ?subject ?predicate ?object WHERE {?subject ?predicate ?object}";

   /**
    * Serial version id.
    */
   private static final long serialVersionUID = 1L;

   /**
    * The scroll pane which encompasses the table.
    */
   private JScrollPane my_statementTableScrollPane;

   /**
    * The table to display the model data in.
    */
   private JTable my_statementTable;

   /**
    * This panel holds the buttons.
    */
   private JPanel my_buttonPanel;

   /**
    * The refresh button.
    */
   private JButton my_refreshButton;

//   /**
//    * Allow the user to enter a custom query, the results of which will be
//    * displayed in the table.
//    */
//   private JTextField my_queryTextField;

//   /**
//    * The component that owns this UI.
//    */
//   private final DataStoreManager my_owner;

   /**
    * Create and inititalise a ModelViewerGUI.
    * 
    * @param the_owner
    *           The UserApplication that owns this UI.
    */
   public ViewerPanel(final DataStoreManager the_owner) {
      super();
      //my_owner = the_owner;
      initGUI();
   }

   /**
    * This method initializes the GUI.
    */
   private void initGUI() {
      setLayout(new java.awt.BorderLayout());
      add(getButtonPanel(), java.awt.BorderLayout.SOUTH);
      add(getStatementTableScrollPane(), java.awt.BorderLayout.CENTER);
//      add(getQueryTextField(), java.awt.BorderLayout.NORTH);
   }

   /**
    * This method initializes my_buttonPanel.
    * 
    * @return javax.swing.JPanel
    */
   private JPanel getButtonPanel() {
      if (my_buttonPanel == null) {
         my_buttonPanel = new JPanel();
         my_buttonPanel.setBorder(javax.swing.BorderFactory
               .createEtchedBorder(javax.swing.border.EtchedBorder.RAISED));
         my_buttonPanel.add(getRefreshButton(), null);
      }
      return my_buttonPanel;
   }

   /**
    * This method initializes my_refreshButton.
    * 
    * @return javax.swing.JButton
    */
   private JButton getRefreshButton() {
      if (my_refreshButton == null) {
         my_refreshButton = new JButton();
         my_refreshButton.setText("Refresh View");
         my_refreshButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(final java.awt.event.ActionEvent an_event) {
               final TableModel theModel = getStatementTable().getModel();
               if (theModel instanceof DataStoreMetadataTableModelAdaptor) {
                  final DataStoreMetadataTableModelAdaptor metaTableModel
                     = (DataStoreMetadataTableModelAdaptor) theModel;
                  metaTableModel.refresh();
               }
            }
         });
      }
      return my_refreshButton;
   }

//   /**
//    * This method initializes my_queryTextField.
//    * 
//    * @return javax.swing.JTextField
//    */
//   private JTextField getQueryTextField() {
//      if (my_queryTextField == null) {
//         my_queryTextField = new JTextField();
//         my_queryTextField.setText(QUERY_ALL_DATA);
//         my_queryTextField.addActionListener(new java.awt.event.ActionListener() {
//            public void actionPerformed(final java.awt.event.ActionEvent an_event) {
//               String queryString = my_queryTextField.getText();
//               try {
//                  QueryFactory.create(my_queryTextField.getText());
////                  my_owner.setQuery(queryString);
//               } catch (QueryException ex) {
//                  queryString = QUERY_ALL_DATA;
//                  my_queryTextField.setText(QUERY_ALL_DATA);
//               }
//            }
//         });
//      }
//      return my_queryTextField;
//   }

   /**
    * This method initializes my_statementTableScrollPane.
    * 
    * @return javax.swing.JScrollPane
    */
   private JScrollPane getStatementTableScrollPane() {
      if (my_statementTableScrollPane == null) {
         my_statementTableScrollPane = new JScrollPane();
         my_statementTableScrollPane.setViewportView(getStatementTable());
      }
      return my_statementTableScrollPane;
   }

   /**
    * This method initializes my_statementTable.
    * 
    * @return javax.swing.JTable
    */
   private JTable getStatementTable() {
      if (my_statementTable == null) {
         my_statementTable = new JTable();
      }
      return my_statementTable;
   }

   /**
    * Set the model that this viewer will display.
    * 
    * @param a_tableModel
    *           The model to display in the viewer window.
    */
   public final void setTableModel(final TableModel a_tableModel) {
      getStatementTable().setModel(a_tableModel);
   }
}
