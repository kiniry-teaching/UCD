	/**
	 * This  class is used to test run the classes  for the Hardware interface 
	 * components of the SelfChekcOut project.
	 * <p>
	 * 
	 * @author Peter Gibney
	 * @version 20th March 2008.
	 */
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

public class ShowBarCode extends JFrame {
	private BarCodePanels bcp;
	// ------------------------------------------------------
	public ShowBarCode() {
		super("Hardware Interface -SelfCheckOut");
		Container c = getContentPane();
		c.setLayout(new BorderLayout());
		bcp = new BarCodePanels(); // the sequence of snaps appear here
		c.add(bcp, "Center");
		addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent e) {
				bcp.closeDown();
				System.exit(0);
			}
		});

		pack();
		setResizable(false);
		setVisible(true);
	}
	// ------------------------------------------------------
	public static void main(String args[]) {
		/*
		byte b = -120;
		
		for (int step = 0; step < 500; step++) {
			b++;
			System.out.println("Byte = " + b + ", Val = " + ((256 + (int) b) % 256));
		}
		System.exit(0);
		*/
		new ShowBarCode();
	}
}
