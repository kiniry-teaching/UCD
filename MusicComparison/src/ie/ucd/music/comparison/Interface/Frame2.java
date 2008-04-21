//frame2
 
package ie.ucd.music.comparison.Interface;
 
import java.awt.BorderLayout;
import javax.swing.JFrame;
import javax.swing.JButton;
import java.awt.*;
import com.borland.jbcl.layout.XYLayout;
import com.borland.jbcl.layout.*;
import javax.swing.JProgressBar;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JLabel;
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
public class Frame2 extends JFrame {
    XYLayout xYLayout1 = new XYLayout();
    JButton Cancel = new JButton();
   
    JLabel jLabel1 = new JLabel();
    public Frame2() {
        try {
            jbInit();
        } catch (Exception exception) {
            exception.printStackTrace();
        }
    }
    private void jbInit() throws Exception {
        getContentPane().setLayout(xYLayout1);
        setSize(new Dimension(400, 300));
        this.getContentPane().setBackground(SystemColor.control);
        Cancel.setText("Cancel");
        Cancel.addActionListener(new Frame2_Cancel_actionAdapter(this));
        jLabel1.setText("There were no duplicates found");
        this.getContentPane().add(jLabel1, new XYConstraints(42, 76, 309, 25));
        this.getContentPane().add(Cancel, new XYConstraints(310, 197, 80, 40));
    }
    public void Cancel_actionPerformed(ActionEvent e) {
        System.exit(0);
    }
}

class Frame2_Cancel_actionAdapter implements ActionListener {
    private Frame2 adaptee;
    Frame2_Cancel_actionAdapter(Frame2 adaptee) {
        this.adaptee = adaptee;
    }
    public void actionPerformed(ActionEvent e) {
        adaptee.Cancel_actionPerformed(e);
    }
}