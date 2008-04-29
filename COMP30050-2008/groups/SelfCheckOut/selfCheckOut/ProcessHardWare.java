package selfCheckOut;
	/**
	 * This class is used to grab using a camera the bacodes and to transmit
	 * the to the main program, the command line must include the IP address
	 * of the virtual machine that is running the server for the scales.
	 * components of the SelfChekcOut project.
	 * <p>
	 * 
	 * @author Peter Gibney
	 * @version 20th March 2008.
	 */
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;


public class ProcessHardWare extends JFrame {
	private static final long serialVersionUID = 8374729;
	private BarCodePanels bcp;
	// ------------------------------------------------------
	public ProcessHardWare(String AddressIP) {
		super("Hardware Interface -SelfCheckOut");
		Container c = getContentPane();
		c.setLayout(new BorderLayout());
		bcp = new BarCodePanels(AddressIP); // the sequence of snaps appear here
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
		new ProcessHardWare(args[0]);
	}
}
