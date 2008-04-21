//Music Program
 
package ie.ucd.music.comparison.Interface;

import ie.ucd.music.comparison.Database.MusicItem;
import java.awt.Dimension;
import java.awt.Toolkit;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
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
 public class MusicComparisonProgram {
     boolean packFrame = false;
     /**
      * Construct and show the application.
      */
     public MusicComparisonProgram() {
         Frame1 frame = new Frame1();
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
     }
     /**
      * Application entry point.
      *
      * @param args String[]
      */
     public static void main(String[] args) {
      MusicItem[] higher;
      higher = new MusicItem[20];
      MusicItem[] lower;
      lower = new MusicItem[20];
         SwingUtilities.invokeLater(new Runnable() {
             public void run() {
                 try {
                     UIManager.setLookAndFeel(UIManager.
                                              getSystemLookAndFeelClassName());
                 } catch (Exception exception) {
                     exception.printStackTrace();
                 }
                 new MusicComparisonProgram();
             }
         });
     }
 }

