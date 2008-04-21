package ie.ucd.music.comparison.Interface;



    import java.awt.Dimension;
import java.awt.SystemColor;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JProgressBar;

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
    public class Frame2 extends JFrame {
        XYLayout xYLayout1 = new XYLayout();
        JButton Cancel = new JButton();
        JProgressBar jProgressBar1 = new JProgressBar();
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
            jLabel1.setText("Progress");
            this.getContentPane().add(jProgressBar1,
                                      new XYConstraints(43, 106, 318, 38));
            this.getContentPane().add(jLabel1, new XYConstraints(42, 76, 309, 25));
            this.getContentPane().add(Cancel, new XYConstraints(293, 200, 80, 40));
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



