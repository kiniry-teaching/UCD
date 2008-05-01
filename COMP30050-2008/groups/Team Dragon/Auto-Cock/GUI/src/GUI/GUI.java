package GUI;

import java.awt.*;
import javax.swing.*;

import snd.BTSendObject;

import java.awt.event.*;
import java.io.*;
import java.util.Vector;
import java.util.LinkedList;

/**
 * @author Alex Rankin
 *
 */
public class GUI extends JFrame implements ActionListener {

	private JButton preB, cusB, adminB, backBP, backBC, backBA, makeBP, makeBC, addBC,
			remBC, applyBA;
	private JRadioButton stirRB, iceRB, alc1RB, alc2RB, alc3RB;
	private JFrame chFrame, cusFrame, preFrame, adFrame;
	private JPanel contentPanel;
	private JLabel selectL, eSymbol, costL;
	private JTextArea preIngredsList, cusIngredsList;
	private JTextField costP, costC, cost1, cost2, cost3;
	private JComboBox cocktail, cusIngreds, drink1, drink2, drink3;
	private int numIngreds;
	private double cost, temp;
	// List of drinks that can be chosen
	private String[] ingredsList = { "None", "Vodka", "Whiskey", "Malibu", "Gin",
			"Pineapple Juice", "Red Bull", "Coke", "Lime", "Orange Juice",
			"Cranberry Juice" };
	private Beverage bev1, bev2, bev3;
	// Different vectors used to store things
	private Vector<Cocktail> cocktails = new Vector<Cocktail>();
	private Vector<Beverage> bevVec = new Vector<Beverage>();
	private Vector<Beverage> allBevVec = new Vector<Beverage>();
	private Vector<String> ingredsVec = new Vector<String>();
	private Vector<String> cocktailsVec = new Vector<String>();
	private Cocktail none;
	// The BlueTooth object for sending recipes
	BTSendObject send = new BTSendObject();

	/**
	 * Constructor for the GUI class. Initialises cocktails, sets 
	 * up the panel and calls the choice frame
	 */
	public GUI() {
		// Initiate the cocktails
		initCocktails();
		// Setup the content panel
		setupPanel();
		// Open the choice frame
		ChoiceFrame();
	}

	/**
	 * Creates a new JPanel with a white background
	 */
	public void setupPanel() {
		contentPanel = new JPanel();
		contentPanel.setBackground(Color.white);
		contentPanel.setOpaque(true);
	}

	/**
	 * Initialise the cocktails.
	 * Add in any cocktail recipes here
	 */
	public void initCocktails() {
		// Blank cocktail to be selected at first
		none = new Cocktail("None");
		
		// Setup a few cocktail recipes
		Cocktail tempCock = new Cocktail("Vodka + Coke");
		tempCock.addDrink("Coke");
		tempCock.addDrink("Vodka");
		cocktails.add(tempCock);

		tempCock = new Cocktail("Whiskey + Coke");
		tempCock.addDrink("Whiskey");
		tempCock.addDrink("Coke");
		cocktails.add(tempCock);
		
		tempCock = new Cocktail("Malibu + Coke");
		tempCock.addDrink("Malibu");
		tempCock.addDrink("Coke");
		cocktails.add(tempCock);
		
		tempCock = new Cocktail("Screwdriver");
		tempCock.addDrink("Vodka");
		tempCock.addDrink("Orange Juice");
		cocktails.add(tempCock);
		
		tempCock = new Cocktail("Vodka + Red Bull");
		tempCock.addDrink("Vodka");
		tempCock.addDrink("Red Bull");
		cocktails.add(tempCock);
	}

	/**
	 * @param s String name of the beverage to search for
	 * @return The beverage who's name matches the String s
	 */
	public Beverage matchBev(String s) {
		Beverage matchedBev = new Beverage("None", 0, false, 0);
		// Loop around the beverage vector
		for (int i = 0; i < bevVec.size(); i++) {
			// If the name of the beverage matches s, return it
			if (bevVec.get(i).getName().equalsIgnoreCase(s)) {
				matchedBev = bevVec.get(i);
				break;
			}
		}
		return matchedBev;
	}

	/**
	 * @param s String name of cocktail to match
	 * @return Cocktail object which matches the cocktail searched for
	 */
	public Cocktail matchCocktail(String s) {
		// Blank cocktail to return if nothing's found
		Cocktail matchedCocktail = new Cocktail("None");
		// Loop through cocktails
		for (int i = 0; i < cocktails.size(); i++) {
			// Find the cocktail that matches the string
			if (s.equalsIgnoreCase(cocktails.get(i).getName())) {
				// Set the cocktail to be returned and break
				matchedCocktail = cocktails.get(i);
				break;
			}
		}
		// Return the cocktail
		return matchedCocktail;
	}

	/**
	 * Checks if a beverage is available
	 * 
	 * @param s Name of beverage you want to check
	 * @return True if the beverage is available, else false
	 */
	public boolean bevAvail(String s) {
		// Loop through the beverage vector
		for (int i = 0; i < bevVec.size(); i++) {
			// If you find the beverage, return true
			if (bevVec.get(i).getName().equalsIgnoreCase(s)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Sets the available drinks
	 */
	public void setAvail() {
		// Clear the ingredients vector
		ingredsVec.clear();
		for (int i = 0; i < bevVec.size(); i++) {
			// Add the names of the beverages available to the ingredients vector
			ingredsVec.add(bevVec.get(i).getName());
		}
		// Setup available cocktails
		cocktailsAvail();
	}

	/**
	 * Reset the drinks available
	 */
	public void resetDrinks() {
		// Loop through all the beverages
		for (int i = 0; i < allBevVec.size(); i++) {
			// Set the beverage to false
			allBevVec.get(i).setAvailable(false);
		}
	}

	/**
	 * Set the available cocktails
	 */
	public void cocktailsAvail() {
		// Clear the cocktails vector
		cocktailsVec.clear();
		// Add the "None" cocktail to the vector
		cocktailsVec.add(none.getName());
		// Loop through cocktails
		for (int i = 0; i < cocktails.size(); i++) {
			// Set toCheck to the list of beverages from this cocktail
			LinkedList<String> toCheck = cocktails.get(i).getList();
			// Loop through the beverages that make this cocktail
			for (int j = 0; j < toCheck.size(); j++) {
				// Check if the beverage is available
				if (!bevAvail(toCheck.get(j))) {
					// If it isn't, set false and break
					cocktails.get(i).setAvail(false);
					break;
				} else {
					// If it is, set true and continue looping
					cocktails.get(i).setAvail(true);
				}
			}
			// If the cocktail is available
			if (cocktails.get(i).getAvail()) {
				// Add it to the available cocktails
				cocktailsVec.add(cocktails.get(i).getName());
			}
		}
	}

	/**
	 * Update the custom cost
	 */
	public void updateCCost() {
		temp = cost / 100;
		costC.setText(Double.toString(temp));
	}

	/**
	 * Sets up the administration frame
	 */
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
		adFrame.setSize(600, 400);

		// Cost lable
		costL = new JLabel("Cost");
		costL.setLocation(390, 50);
		costL.setSize(100, 30);

		// Setup drink 1 combobox
		drink1 = new JComboBox(ingredsList);
		drink1.setLocation(50, 80);
		drink1.setSize(200, 30);
		drink1.setSelectedIndex(0);
		drink1.addActionListener(this);

		// Alcoholic 1 radio button
		alc1RB = new JRadioButton("Alcoholic?", false);
		alc1RB.setLocation(270, 80);
		alc1RB.setSize(100, 30);
		alc1RB.setOpaque(false);
		alc1RB.addActionListener(this);

		// Cost 1 text field
		cost1 = new JTextField("0");
		cost1.setLocation(390, 80);
		cost1.setSize(100, 30);
		cost1.setHorizontalAlignment(JTextField.RIGHT);

		// Setup drink 2 combobox
		drink2 = new JComboBox(ingredsList);
		drink2.setLocation(50, 120);
		drink2.setSize(200, 30);
		drink2.setSelectedIndex(0);
		drink2.addActionListener(this);

		// Alcoholic 2 radio button
		alc2RB = new JRadioButton("Alcoholic?", false);
		alc2RB.setLocation(270, 120);
		alc2RB.setSize(100, 30);
		alc2RB.setOpaque(false);
		alc2RB.addActionListener(this);

		// Cost 2 text field
		cost2 = new JTextField("0");
		cost2.setLocation(390, 120);
		cost2.setSize(100, 30);
		cost2.setHorizontalAlignment(JTextField.RIGHT);

		// Setup drink 3 combobox
		drink3 = new JComboBox(ingredsList);
		drink3.setLocation(50, 160);
		drink3.setSize(200, 30);
		drink3.setSelectedIndex(0);
		drink3.addActionListener(this);

		// Alcoholic 3 radio button
		alc3RB = new JRadioButton("Alcoholic?", false);
		alc3RB.setLocation(270, 160);
		alc3RB.setSize(100, 30);
		alc3RB.setOpaque(false);
		alc3RB.addActionListener(this);

		// Cost 3 text field
		cost3 = new JTextField("0");
		cost3.setLocation(390, 160);
		cost3.setSize(100, 30);
		cost3.setHorizontalAlignment(JTextField.RIGHT);

		// The back button
		backBA = new JButton("Back");
		backBA.setLocation(50, 320);
		backBA.setSize(100, 30);
		backBA.addActionListener(this);

		// The apply button
		applyBA = new JButton("Apply");
		applyBA.setLocation(390, 320);
		applyBA.setSize(100, 30);
		applyBA.addActionListener(this);

		// Add eveerything to the frame
		adFrame.add(costL);
		adFrame.add(drink1);
		adFrame.add(alc1RB);
		adFrame.add(cost1);
		adFrame.add(drink2);
		adFrame.add(alc2RB);
		adFrame.add(cost2);
		adFrame.add(drink3);
		adFrame.add(alc3RB);
		adFrame.add(cost3);
		adFrame.add(backBA);
		adFrame.add(applyBA);

		// Make the frame visible
		adFrame.setVisible(true);
	}

	/**
	 * Sets up the choice frame
	 */
	public void ChoiceFrame() {
		chFrame = new JFrame("Auto-Cock");
		chFrame.setContentPane(contentPanel);
		chFrame.setResizable(false);

		// Setup the images
		ImageIcon preButtonI = new ImageIcon("images/premadeB.jpg");
		ImageIcon cusButtonI = new ImageIcon("images/customB.jpg");

		// Add a window listener for close button
		chFrame.addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent e) {
				System.exit(0);
			}
		});

		chFrame.setLayout(null);
		chFrame.setSize(600, 400);

		// The select label
		selectL = new JLabel("Please Select a Section");
		selectL.setLocation(225, 40);
		selectL.setSize(150, 20);
		
		// The premade cocktail button
		preB = new JButton(preButtonI);
		preB.setLocation(112, 100);
		preB.setSize(160, 200);
		preB.addActionListener(this);
		
		// The custom cocktail button
		cusB = new JButton(cusButtonI);
		cusB.setLocation(337, 100);
		cusB.setSize(160, 200);
		cusB.addActionListener(this);
		
		// The admin panel button
		adminB = new JButton("Admin Panel");
		adminB.setLocation(220, 310);
		adminB.setSize(160, 30);
		adminB.addActionListener(this);

		// Add everything to the frame
		chFrame.add(selectL);
		chFrame.add(preB);
		chFrame.add(cusB);
		chFrame.add(adminB);
		
		// Make the frame visible
		chFrame.setVisible(true);
	}

	/**
	 * Sets up the premade drinks frame
	 */
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
		preFrame.setSize(600, 400);

		// Combobox for the cocktail list
		cocktail = new JComboBox(cocktailsVec);
		cocktail.setLocation(50, 80);
		cocktail.setSize(200, 30);
		cocktail.setSelectedIndex(0);
		cocktail.addActionListener(this);

		// The back button
		backBP = new JButton("Back");
		backBP.setLocation(50, 320);
		backBP.setSize(100, 30);
		backBP.addActionListener(this);

		// The list of ingredients in this cocktail
		preIngredsList = new JTextArea(250, 240);
		preIngredsList.setLocation(300, 80);
		preIngredsList.setLineWrap(false);
		preIngredsList.setRows(10);
		preIngredsList.setSize(250, 240);
		preIngredsList.setEditable(false);
		preIngredsList.setText("Ingredients");

		// Euro symbol
		eSymbol = new JLabel("€");
		eSymbol.setLocation(330, 320);
		eSymbol.setSize(20, 30);

		// The cost
		costP = new JTextField();
		costP.setLocation(350, 320);
		costP.setSize(100, 30);
		costP.setEditable(false);
		costP.setHorizontalAlignment(JTextField.RIGHT);

		// The make button
		makeBP = new JButton("Make");
		makeBP.setLocation(450, 320);
		makeBP.setSize(100, 30);
		makeBP.addActionListener(this);

		// Add everything
		preFrame.add(backBP);
		preFrame.add(cocktail);
		preFrame.add(preIngredsList);
		preFrame.add(eSymbol);
		preFrame.add(costP);
		preFrame.add(makeBP);

		// Make the frame visible
		preFrame.setVisible(true);
	}

	/**
	 * Sets up the custom drinks frame
	 */
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
		cusFrame.setSize(600, 400);

		// Number of ingredients and cost to 0
		numIngreds = 0;
		cost = 0;

		// The combobox of ingredients
		cusIngreds = new JComboBox(ingredsVec);
		cusIngreds.setLocation(50, 80);
		cusIngreds.setSize(200, 30);
		cusIngreds.setSelectedIndex(0);
		cusIngreds.addActionListener(this);

		// The add button
		addBC = new JButton("Add");
		addBC.setLocation(50, 120);
		addBC.setSize(100, 30);
		addBC.addActionListener(this);

		// The remove button
		remBC = new JButton("Remove");
		remBC.setLocation(50, 160);
		remBC.setSize(100, 30);
		remBC.addActionListener(this);

		// The stir radio button
		stirRB = new JRadioButton("Stir?", false);
		stirRB.setLocation(50, 200);
		stirRB.setSize(100, 30);
		stirRB.setOpaque(false);
		stirRB.addActionListener(this);

		// The ice radio button
		iceRB = new JRadioButton("Ice?", false);
		iceRB.setLocation(50, 230);
		iceRB.setSize(100, 30);
		iceRB.setOpaque(false);
		iceRB.addActionListener(this);

		// The back button
		backBC = new JButton("Back");
		backBC.setLocation(50, 320);
		backBC.setSize(100, 30);
		backBC.addActionListener(this);

		// The list of selected ingredients
		cusIngredsList = new JTextArea(250, 240);
		cusIngredsList.setLocation(300, 80);
		cusIngredsList.setLineWrap(false);
		cusIngredsList.setRows(10);
		cusIngredsList.setSize(250, 240);
		cusIngredsList.setEditable(false);

		// The euro symbol
		eSymbol = new JLabel("€");
		eSymbol.setLocation(330, 320);
		eSymbol.setSize(20, 30);

		// The cost field
		costC = new JTextField();
		costC.setLocation(350, 320);
		costC.setSize(100, 30);
		costC.setEditable(false);
		costC.setHorizontalAlignment(JTextField.RIGHT);

		// The make button
		makeBC = new JButton("Make");
		makeBC.setLocation(450, 320);
		makeBC.setSize(100, 30);
		makeBC.addActionListener(this);

		// Add everything to the frame
		cusFrame.add(cusIngreds);
		cusFrame.add(addBC);
		cusFrame.add(remBC);
		cusFrame.add(stirRB);
		cusFrame.add(iceRB);
		cusFrame.add(backBC);
		cusFrame.add(cusIngredsList);
		cusFrame.add(eSymbol);
		cusFrame.add(costC);
		cusFrame.add(makeBC);

		// Update the cost and make the frame visible
		updateCCost();
		cusFrame.setVisible(true);
	}

	/* (non-Javadoc)
	 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
	 */
	public void actionPerformed(ActionEvent aE) {
		// Store the source of the action
		Object src = aE.getSource();
		
		// If statements to determine what to do
		if (src == preB) {
			// Check that there are cocktails available
			if (!cocktailsVec.isEmpty()) {
				chFrame.setVisible(false);
				setupPanel();
				PremadeFrame();
			}
		} else if (src == cusB) {
			// Check that there are beverages available
			if (!bevVec.isEmpty()) {
				chFrame.setVisible(false);
				setupPanel();
				CustomFrame();
			}
		} else if (src == adminB) {
			// Open the admin panel
			chFrame.setVisible(false);
			setupPanel();
			AdminFrame();
		} else if (src == backBA) {
			// Go back to the choice panel
			adFrame.setVisible(false);
			setupPanel();
			chFrame.setVisible(true);
		} else if (src == backBP) {
			// Go back to the choice panel
			preFrame.setVisible(false);
			setupPanel();
			chFrame.setVisible(true);
		} else if (src == backBC) {
			// Go back to the choice panel
			cusFrame.setVisible(false);
			setupPanel();
			chFrame.setVisible(true);
		} else if (src == makeBP) {
			//System.out.println("Making your drink!");
			// Get the selected cocktail
			Cocktail selected = matchCocktail((String) cocktail
					.getSelectedItem());
			// Make an int array with the proper beverage ID's
			int[] toSend = selected.getArray(bevVec);
			// Send the array
			send.startClient(toSend);
			send.stopClient();
		} else if (src == makeBC) {
			// Make sure there are ingredients selected
			if (numIngreds != 0) {
				//System.out.println("Making your drink!");
				// Read in the list of ingredients
				BufferedReader in = new BufferedReader(new StringReader(
						cusIngredsList.getText()));
				String line;
				// Create an array to store the beverage ID's
				int[] position = new int[numIngreds + 2];
				try {
					for (int i = 0; i < numIngreds; i++) {
						// Read in a line
						line = in.readLine();
						// Match the string ingredient to the beverage
						Beverage tempBev = matchBev(line);
						// Get the ID of the beverage and add it to the array
						position[i] = tempBev.getId();
					}
				} catch (Exception e) {
				}
				if (iceRB.isSelected()) {
					// 0 for ice
					position[numIngreds] = 0;
				} else {
					// 99 means skip
					position[numIngreds] = 99;
				}
				if (stirRB.isSelected()) {
					// 1 for stirring
					position[numIngreds + 1] = 1;
				} else {
					// 99 means skip
					position[numIngreds + 1] = 99;
				}
				// Send the array
				send.startClient(position);
				send.stopClient();
			}
		} else if (src == addBC) {
			// Max 5 ingredients
			if (numIngreds < 6) {
				// Get the selected item
				String selIngred = (String) cusIngreds.getSelectedItem();
				// Append it to the list
				cusIngredsList.append(selIngred + "\n");
				// Increment the number of ingredients
				numIngreds++;
				// Get the cost of that ingredient
				cost += matchBev(selIngred).getPrice();
				// Update the cost
				updateCCost();
			} else {
				// In case you selected too many ingredients
				System.out
						.println("Too many ingredients. Please remove one if you would like to add more.");
			}
		} else if (src == remBC) {
			// Get the selected ingredient
			String selIngred = (String) cusIngreds.getSelectedItem();
			// Read in the list of current ingredients
			BufferedReader in = new BufferedReader(new StringReader(
					cusIngredsList.getText()));
			String line;
			String toUpdate = "";
			// Bool to check if the ingredient was removed
			boolean removed = false;
			try {
				// Read in a line
				while ((line = in.readLine()) != null) {
					// Check if the line is equal to the ingredient to remove
					if (line.equalsIgnoreCase(selIngred) && removed == false) {
						//System.out.println("Removing: " + selIngred + "\n");
						// Match ingredient to beverage and adjust the price
						cost -= matchBev(selIngred).getPrice();
						updateCCost();
						// Decrement the ingredients
						numIngreds--;
						// Ingredient was removed
						removed = true;
					} else {
						// Store the rest of the ingredients that weren't removed
						toUpdate = toUpdate + line + "\n";
					}
				}
			} catch (IOException e) {

			}
			// Update the ingredients
			cusIngredsList.setText(toUpdate);
		} else if (src == cocktail) {
			// Store the combo box in a temp object
			JComboBox tempBox = (JComboBox) src;
			// Get the selected drink
			String drink = (String) tempBox.getSelectedItem();
			// Match that drink with the cocktail
			Cocktail selected = matchCocktail(drink);
			// Calculate the price using the beverages available
			selected.calcPrice(bevVec);
			Double tempCost = Double.valueOf(selected.getPrice() / 100)
					.doubleValue();
			// Update cost box
			costP.setText(String.valueOf(tempCost));
			// Clear ingredients list
			preIngredsList.setText("");
			// Get the list of ingredients
			LinkedList<String> list = selected.getList();
			// Update the ingredients list
			for (int i = 0; i < list.size(); i++) {
				preIngredsList.append(list.get(i) + "\n");
			}
		} else if (src == applyBA) {
			Double tempCost;
			int tempCost2;
			// Reset the old beverages and vectors
			resetDrinks();
			bevVec.clear();
			cocktailsVec.clear();

			// Store the drink 1 combo box in a temp object
			JComboBox tempBox = (JComboBox) drink1;
			// Check it isn't "None" and there's a cost
			if ((String) tempBox.getSelectedItem() == "None"
					|| cost1.getText() == "") {
				// System.out.println("Choose a drink and put in a price.");
			} else {
				// Calculate cost
				tempCost = Double.valueOf(cost1.getText()).doubleValue();
				tempCost2 = (int) (tempCost * 100);
				// Create the new beverage and add it to the available beverages
				bev1 = new Beverage((String) tempBox.getSelectedItem(),
						tempCost2, alc1RB.isSelected(), 1);
				bevVec.add(bev1);
			}

			// Store the drink 2 combo box in a temp object
			tempBox = (JComboBox) drink2;
			// Check it isn't "None" and there's a cost
			if ((String) tempBox.getSelectedItem() == "None"
					|| cost2.getText() == "") {
				// System.out.println("Choose a drink and put in a price.");
			} else {
				// Calculate cost
				tempCost = Double.valueOf(cost2.getText()).doubleValue();
				tempCost2 = (int) (tempCost * 100);
				// Create the new beverage and add it to the available beverages
				bev2 = new Beverage((String) tempBox.getSelectedItem(),
						tempCost2, alc2RB.isSelected(), 2);
				bevVec.add(bev2);
			}

			// Store the drink 3 combo box in a temp object
			tempBox = (JComboBox) drink3;
			// Check it isn't "None" and there's a cost
			if ((String) tempBox.getSelectedItem() == "None"
					|| cost3.getText() == "") {
				// System.out.println("Choose a drink and put in a price.");

			} else {
				// Calculate cost
				tempCost = Double.valueOf(cost3.getText()).doubleValue();
				tempCost2 = (int) (tempCost * 100);
				// Create the new beverage and add it to the available beverages
				bev3 = new Beverage((String) tempBox.getSelectedItem(),
						tempCost2, alc3RB.isSelected(), 3);
				bevVec.add(bev3);
			}
			// Call set available
			setAvail();
		}
	}

}
