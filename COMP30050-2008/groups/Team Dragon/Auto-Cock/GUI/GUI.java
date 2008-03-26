import java.awt.*;
import javax.swing.*;
import java.awt.event.*;
import java.io.*;

public class GUI extends JFrame implements ActionListener{

	JButton preB, cusB, adminB, backBP, backBC, backBA, makeBP, makeBC, addBC, remBC;
	JRadioButton stirRB;
	JFrame chFrame, cusFrame, preFrame, adFrame;
	JPanel contentPanel;
	JLabel selectL, eSymbol;
	JTextArea preIngredsList, cusIngredsList;
	JTextField costP, costC;
	JComboBox cocktail, cusIngreds;
	int numIngreds;
	String[] cocktailsAvail = { "Screwdriver", "Sex on the Beach" };
	String[] ingredsList = { "Vodka", "Whiskey", "Malibu", "Pineapple Juice", "Orange Juice", "Cranberry Juice" };
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		GUI myGUI = new GUI();
		myGUI.setupPanel();
		myGUI.ChoiceFrame();
	}
	
	public void setupPanel() {
		contentPanel = new JPanel();
		contentPanel.setBackground(Color.white);
		contentPanel.setOpaque(true);
	}
	
	public void updateForSelected(String drink) {
		
	}
	
	public void AdminFrame() {
		adFrame = new JFrame("Auto-Cock: Admin Panel");
		adFrame.setContentPane(contentPanel);
		adFrame.setResizable(false);
		
		adFrame.addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent e) {
				System.exit(0);
			}
		});
		adFrame.setLayout(null);
		adFrame.setSize(600,400);
		
		backBA = new JButton("Back");
		backBA.setLocation(50,320);
		backBA.setSize(100,30);
		backBA.addActionListener(this);
		
		adFrame.add(backBA);

		adFrame.setVisible(true);
	}
	
	public void ChoiceFrame() {
		chFrame = new JFrame("Auto-Cock");
		chFrame.setContentPane(contentPanel);
		chFrame.setResizable(false);
		
		ImageIcon preButtonI = new ImageIcon("images/premadeB.jpg");
		ImageIcon cusButtonI = new ImageIcon("images/customB.jpg");

		
		// Add a window listener for close button
		chFrame.addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent e) {
				System.exit(0);
			}
		});

	    chFrame.setLayout(null);
	    chFrame.setSize(600,400);
	    
	    selectL = new JLabel("Please Select a Section");
	    selectL.setLocation(225,40);
	    selectL.setSize(150,20);
	    preB = new JButton(preButtonI);
	    preB.setLocation(112,100);
	    preB.setSize(160,200);
	    preB.addActionListener(this);
	    cusB = new JButton(cusButtonI);
	    cusB.setLocation(337,100);
	    cusB.setSize(160,200);
	    cusB.addActionListener(this);
	    adminB = new JButton("Admin Panel");
	    adminB.setLocation(220, 310);
	    adminB.setSize(160,30);
	    adminB.addActionListener(this);

	    chFrame.add(selectL);
	    chFrame.add(preB);
	    chFrame.add(cusB);
	    chFrame.add(adminB);
	    chFrame.setVisible(true);
	}

	public void PremadeFrame() {
		preFrame = new JFrame("Auto-Cock: Premade Section");
		preFrame.setContentPane(contentPanel);
		preFrame.setResizable(false);
		
		preFrame.addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent e) {
				System.exit(0);
			}
		});
	    preFrame.setLayout(null);
	    preFrame.setSize(600,400);
		
		cocktail = new JComboBox(cocktailsAvail);
		cocktail.setLocation(50,80);
		cocktail.setSize(200,30);
		cocktail.setSelectedIndex(0);
		cocktail.addActionListener(this);
		
		backBP = new JButton("Back");
		backBP.setLocation(50,320);
		backBP.setSize(100,30);
		backBP.addActionListener(this);
		
		preIngredsList = new JTextArea(250,240);
		preIngredsList.setLocation(300,80);
		preIngredsList.setLineWrap(false);
		preIngredsList.setRows(10);
		preIngredsList.setSize(250,240);
		preIngredsList.setEditable(false);
		preIngredsList.setText("Ingredients go here");
		
		eSymbol = new JLabel("€");
		eSymbol.setLocation(330,320);
		eSymbol.setSize(20,30);

		costP = new JTextField();
		costP.setLocation(350,320);
		costP.setSize(100,30);
		costP.setEditable(false);

		makeBP = new JButton("Make");
		makeBP.setLocation(450,320);
		makeBP.setSize(100,30);
		makeBP.addActionListener(this);
		
		preFrame.add(backBP);
		preFrame.add(cocktail);
		preFrame.add(preIngredsList);
		preFrame.add(eSymbol);
		preFrame.add(costP);
		preFrame.add(makeBP);
		
		preFrame.setVisible(true);
	}
	
	public void CustomFrame() {
		cusFrame = new JFrame("Auto-Cock: Custom Section");
		cusFrame.setContentPane(contentPanel);
		cusFrame.setResizable(false);
		
		cusFrame.addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent e) {
				System.exit(0);
			}
		});
	    cusFrame.setLayout(null);
	    cusFrame.setSize(600,400);
	    
	    numIngreds = 0;
	    
		cusIngreds = new JComboBox(ingredsList);
		cusIngreds.setLocation(50,80);
		cusIngreds.setSize(200,30);
		cusIngreds.setSelectedIndex(0);
		cusIngreds.addActionListener(this);
		
		addBC = new JButton("Add");
		addBC.setLocation(50,120);
		addBC.setSize(100,30);
		addBC.addActionListener(this);
		
		remBC = new JButton("Remove");
		remBC.setLocation(50,160);
		remBC.setSize(100,30);
		remBC.addActionListener(this);
		
		stirRB = new JRadioButton("Stir?", false);
		stirRB.setLocation(50, 200);
		stirRB.setSize(100,30);
		stirRB.setOpaque(false);
		stirRB.addActionListener(this);
	    
		backBC = new JButton("Back");
		backBC.setLocation(50,320);
		backBC.setSize(100,30);
		backBC.addActionListener(this);
		
		cusIngredsList = new JTextArea(250,240);
		cusIngredsList.setLocation(300,80);
		cusIngredsList.setLineWrap(false);
		cusIngredsList.setRows(10);
		cusIngredsList.setSize(250,240);
		cusIngredsList.setEditable(false);
		
		eSymbol = new JLabel("€");
		eSymbol.setLocation(330,320);
		eSymbol.setSize(20,30);
		
		costC = new JTextField();
		costC.setLocation(350,320);
		costC.setSize(100,30);
		costC.setEditable(false);
		
		makeBC = new JButton("Make");
		makeBC.setLocation(450,320);
		makeBC.setSize(100,30);
		makeBC.addActionListener(this);
		
		cusFrame.add(cusIngreds);
		cusFrame.add(addBC);
		cusFrame.add(remBC);
		cusFrame.add(stirRB);
		cusFrame.add(backBC);
		cusFrame.add(cusIngredsList);
		cusFrame.add(eSymbol);
		cusFrame.add(costC);
		cusFrame.add(makeBC);
		
		cusFrame.setVisible(true);
	}
	
	public void actionPerformed(ActionEvent aE) {
		Object src = aE.getSource();
		
		if(src == preB) {
			chFrame.setVisible(false);
			setupPanel();
			PremadeFrame();
		}
		else if(src == cusB) {
			chFrame.setVisible(false);
			setupPanel();
			CustomFrame();
		}
		else if(src == adminB) {
			chFrame.setVisible(false);
			setupPanel();
			AdminFrame();
		}
		else if(src == backBA) {
			adFrame.setVisible(false);
			setupPanel();
			chFrame.setVisible(true);
		}
		else if(src == backBP) {
			preFrame.setVisible(false);
			setupPanel();
			chFrame.setVisible(true);
		}
		else if(src == backBC) {
			cusFrame.setVisible(false);
			setupPanel();
			chFrame.setVisible(true);
		}
		else if(src == makeBP) {
			System.out.println("Making your drink!");
		}
		else if(src == makeBC) {
			System.out.println("Making your drink!");
		}
		else if(src == addBC) {
			if(numIngreds < 8) {
				String selIngred = (String)cusIngreds.getSelectedItem();
				cusIngredsList.append(selIngred + "\n");
				numIngreds++;
			}
			else{
				System.out.println("Too many ingredients. Please remove one if you would like to add more.");
			}
		}
		else if(src == remBC) {
			String selIngred = (String)cusIngreds.getSelectedItem();
			BufferedReader in = new BufferedReader(new StringReader(cusIngredsList.getText()));
			String line;
			String toUpdate = "";
			boolean removed = false;
			try {
				while((line = in.readLine()) != null) {
					if(line.equalsIgnoreCase(selIngred) && removed == false) {
						System.out.println("Removing: " + selIngred + "\n");
						removed = true;
					}
					else {
						toUpdate = toUpdate + line + "\n";
					}
				}
			}catch(IOException e) {
				
			}
			cusIngredsList.setText(toUpdate);
		}
		else if(src == cocktail) {
			JComboBox tempBox = (JComboBox)src;
			String drink = (String)tempBox.getSelectedItem();
			System.out.println(drink);
		}
	}
	
}
