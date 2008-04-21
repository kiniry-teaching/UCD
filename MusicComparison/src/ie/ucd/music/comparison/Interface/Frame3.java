package ie.ucd.music.comparison.Interface;





import ie.ucd.music.comparison.Database.*;
import ie.ucd.music.comparison.FindID3.FindID3;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;

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

public class Frame3 extends JFrame {

    XYLayout xYLayout1 = new XYLayout();

    JButton Cancel = new JButton();

    JButton Move = new JButton();

    JButton Show = new JButton();

    JButton Delete = new JButton();

    JLabel jLabel1 = new JLabel();



    public Frame3() {

        try {

            jbInit();

        } catch (Exception exception) {

            exception.printStackTrace();

        }

    }



    private void jbInit() throws Exception {

        getContentPane().setLayout(xYLayout1);

        setSize(new Dimension(400, 300));

        Cancel.setText("Cancel");

        Cancel.addActionListener(new Frame3_Cancel_actionAdapter(this));

        Move.setText("Move");

        Move.addActionListener(new Frame3_Move_actionAdapter(this));

        Show.setText("Show");

        Show.addActionListener(new Frame3_Show_actionAdapter(this));

        Delete.addActionListener(new Frame3_Delete_actionAdapter(this));

        jLabel1.setText(

                "There were duplicates found, what would you like to do with them?");

        Delete.setText("Delete");

        this.getContentPane().add(jLabel1, new XYConstraints(38, 65, 336, 57));

        this.getContentPane().add(Move, new XYConstraints(225, 197, 80, 40));

        this.getContentPane().add(Cancel, new XYConstraints(310, 197, 80, 40));

        this.getContentPane().add(Delete, new XYConstraints(140, 197, 80, 40));

        this.getContentPane().add(Show, new XYConstraints(55, 197, 80, 40));

    }



    public void Cancel_actionPerformed(ActionEvent e) {

        System.exit(0);

    }



    public void Move_actionPerformed(ActionEvent e) {

        System.out.println("The Move command was pressed");

        JOptionPane.showMessageDialog(this, "The move button was pressed i will now move the files");

    }



    public void Show_actionPerformed(ActionEvent e) {

        MusicItem[] higher;

        higher = new MusicItem[20];

        MusicItem[] lower;

        lower = new MusicItem[20];
        
        Query.findDuplicates(higher, lower);
        

        for (int i = 0; i < 20; i++){

                //JOptionPane.showMessageDialog(this, "Aritist:"+higher.getArtist[i]+" Song:"+higher.getSong[i]+" Bitrate:"+higher.getBitrate[i]+" is similar to "+" Aritist:"+lower.getArtist[i]+" Song:"+lower.getSong[i]+" Bitrate:"+lower.getBitrate[i]);

        

        Object[] options = { "Next", "Delete",}; 

        int result = JOptionPane.showOptionDialog(this, "Aritist:"+higher[i].getArtist()+" Song:"+higher[i].getSong()+" Bitrate:"+higher[i].getBitRate()+" is similar to "+" Aritist:"+lower[i].getArtist()+" Song:"+lower[i].getSong()+" Bitrate:"+lower[i].getBitRate() + 

                "", "Pick an Option", JOptionPane.DEFAULT_OPTION, 

                 JOptionPane.QUESTION_MESSAGE, null, options, options[0]);

        if(options[result] == options[1]){

                String fileName = lower[i].getfileName();

                FindID3.DeleteFile(fileName);

        }

        //FindID3.DeleteFile("C:\1\Mika - Realx, Take It Easy");



        //JOptionPane.showMessageDialog(this, "Aritist: Beatles Song: Penny Lane Bitrate: 256 is similar to Aritist:The Beatles Song: Penny Lane Bitrate: 128");

        System.out.println("The Show command was pressed");

        JOptionPane.showMessageDialog(this, "The Show button was pressed i will now Show you the similar files");

    }

   }





    public void Delete_actionPerformed(ActionEvent e) {

        /*String fileName = "file.txt";

    // A File object to represent the filename

    File f = new File(fileName);



    boolean success = f.delete();



    if (!success)

      throw new IllegalArgumentException("Delete: deletion failed");*/





        System.out.println("The Delete command was pressed");

        JOptionPane.showMessageDialog(this, "The delete button was pressed i will now delete the files");

    }

}





class Frame3_Delete_actionAdapter implements ActionListener {

    private Frame3 adaptee;

    Frame3_Delete_actionAdapter(Frame3 adaptee) {

        this.adaptee = adaptee;

    }



    public void actionPerformed(ActionEvent e) {

        adaptee.Delete_actionPerformed(e);

    }

}





class Frame3_Cancel_actionAdapter implements ActionListener {

    private Frame3 adaptee;

    Frame3_Cancel_actionAdapter(Frame3 adaptee) {

        this.adaptee = adaptee;

    }



    public void actionPerformed(ActionEvent e) {

        adaptee.Cancel_actionPerformed(e);

    }

}





class Frame3_Move_actionAdapter implements ActionListener {

    private Frame3 adaptee;

    Frame3_Move_actionAdapter(Frame3 adaptee) {

        this.adaptee = adaptee;

    }



    public void actionPerformed(ActionEvent e) {

        adaptee.Move_actionPerformed(e);

    }

}



class Frame3_Show_actionAdapter implements ActionListener {

    private Frame3 adaptee;

    Frame3_Show_actionAdapter(Frame3 adaptee) {

        this.adaptee = adaptee;

    }



    public void actionPerformed(ActionEvent e) {

        adaptee.Show_actionPerformed(e);

    }

}



