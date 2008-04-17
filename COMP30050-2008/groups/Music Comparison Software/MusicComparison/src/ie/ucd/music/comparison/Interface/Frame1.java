package ie.ucd.music.comparison.Interface;

 


import ie.ucd.music.comparison.FindID3.FindID3;

import java.awt.Dimension;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextField;

import com.borland.jbcl.layout.XYConstraints;
import com.borland.jbcl.layout.XYLayout;

/**
 * <p>Title: </p>
 *
 * <p>Description: </p>
 *
 * <p>Copyright: Copyright (c) 2008</p>
 *
 * <p>Company: </p>
 *
 * @author not attributable
 * @version 1.0
 */
public class Frame1 extends JFrame {
    boolean packFrame = false;
    JPanel contentPane;
    JMenuBar jMenuBar1 = new JMenuBar();
    JMenu jMenuFile = new JMenu();
    JMenuItem jMenuFileExit = new JMenuItem();
    /*ImageIcon image1 = new ImageIcon(interfac.Frame1.class.getResource(
            "openFile.png"));
    ImageIcon image2 = new ImageIcon(interfac.Frame1.class.getResource(
            "closeFile.png"));
    ImageIcon image3 = new ImageIcon(interfac.Frame1.class.getResource(
            "help.png"));*/
    XYLayout xYLayout1 = new XYLayout();
    JButton Run = new JButton();
    JButton Cancel = new JButton();
    JTextField Input1 = new JTextField();
    JTextField Input2 = new JTextField();
    JLabel jLabel1 = new JLabel();
    String I1 = "";
    String I2 = "";
    private FindID3 findid3;

   
    public Frame1() {
     I1 = Input1.getText();
     I2 = Input2.getText();
     
        try {
            setDefaultCloseOperation(EXIT_ON_CLOSE);
            jbInit();
        } catch (Exception exception) {
            exception.printStackTrace();
        }
    }

    /**
     * Component initialization.
     *
     * @throws java.lang.Exception
     */
    private void jbInit() throws Exception {
        contentPane = (JPanel) getContentPane();
        contentPane.setLayout(xYLayout1);
        setSize(new Dimension(400, 300));
        setTitle("Main Menu");
        jMenuFile.setText("File");
        jMenuFileExit.setText("Exit");
        jMenuFileExit.addActionListener(new Frame1_jMenuFileExit_ActionAdapter(this));
        Run.setText("Run");
        Run.addActionListener(new Frame1_Run_actionAdapter(this));
        Cancel.setText("Cancel");
        Cancel.addActionListener(new Frame1_Cancel_actionAdapter(this));
        Input1.setToolTipText("");
        Input1.setText("");
        Input2.setToolTipText("");
        Input2.setText("");
        //I1 = Input1.getText();
        //I2 = Input2.getText();
        jLabel1.setText(
                "Please enter two different directories to be searched for mp3 files");
        jMenuBar1.add(jMenuFile);
        jMenuFile.add(jMenuFileExit);
        setJMenuBar(jMenuBar1);
        contentPane.add(Run, new XYConstraints(219, 172, 80, 40));
        contentPane.add(Cancel, new XYConstraints(305, 173, 80, 40));
        contentPane.add(Input2, new XYConstraints(196, 41, 187, 40));
        contentPane.add(Input1, new XYConstraints(2, 41, 188, 40));
        contentPane.add(jLabel1, new XYConstraints(10, 16, 376, 22));
    }

    /**
     * File | Exit action performed.
     *
     * @param actionEvent ActionEvent
     */
    void jMenuFileExit_actionPerformed(ActionEvent actionEvent) {
        System.exit(0);
    }

    public void Run_actionPerformed(ActionEvent e) {
        //frame.setVisible(false);
     I1 = Input1.getText();
     I2 = Input2.getText();
     System.out.println(I1);
     System.out.println(I2);
     if(Input1.getText().length() == 0 || Input2.getText().length() == 0){
      JOptionPane.showMessageDialog(this, "Please enter two directories");
      System.out.println("Please enter two directories");
     }
     else{
    	 findid3.FindDirectory(I1,I2);
    	 
    	 Frame3 frame = new Frame3();
       // Validate frames that have preset sizes
       // Pack frames that have useful preferred size info, e.g. from their layout
       if (packFrame) {
           frame.pack();
       } else {
           frame.validate();
       }
       // Center the window
       Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
       Dimension frameSize = frame.getSize();
       if (frameSize.height > screenSize.height) {
           frameSize.height = screenSize.height;
       }
       if (frameSize.width > screenSize.width) {
           frameSize.width = screenSize.width;
       }
       frame.setLocation((screenSize.width - frameSize.width) / 2,
                         (screenSize.height - frameSize.height) / 2);

       frame.setVisible(true);
       System.out.println("The Run command was pressed");
        //JOptionPane.showMessageDialog(this, "The Run command was pressed");
     }
    }

    public void Cancel_actionPerformed(ActionEvent e) {
        System.exit(0);
    }
}


class Frame1_Cancel_actionAdapter implements ActionListener {
    private Frame1 adaptee;
    Frame1_Cancel_actionAdapter(Frame1 adaptee) {
        this.adaptee = adaptee;
    }

    public void actionPerformed(ActionEvent e) {
        adaptee.Cancel_actionPerformed(e);
    }
}


class Frame1_Run_actionAdapter implements ActionListener {
    private Frame1 adaptee;
    Frame1_Run_actionAdapter(Frame1 adaptee) {
        this.adaptee = adaptee;
    }

    public void actionPerformed(ActionEvent e) {

        adaptee.Run_actionPerformed(e);
    }
}


class Frame1_jMenuFileExit_ActionAdapter implements ActionListener {
    Frame1 adaptee;

    Frame1_jMenuFileExit_ActionAdapter(Frame1 adaptee) {
        this.adaptee = adaptee;
    }

    public void actionPerformed(ActionEvent actionEvent) {
        adaptee.jMenuFileExit_actionPerformed(actionEvent);
    }
}

