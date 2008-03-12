
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

public class ShowBarCode extends JFrame {
	private BarCodePanels bcp;

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

	public static void main(String args[]) {
		new ShowBarCode();
	}
}
