package ui;
import javax.swing.*;
import java.awt.event.*;
import java.awt.*;

public class Interface extends JFrame implements ActionListener
{
	static final long serialVersionUID=0;
	public int customerNr; //number customer enters
	public String customerNrString;
	public String customerName;
	public String itemName; //item name to be displayed 
	public double itemPrice; //item price to be displayed
	public String itemAllergies;
	public double subTotal;
	public double previousSubTotal;
	public double total; //total amount charged for a transaction
	public double amountTendered; //amount tendered for a transaction
	public double change; //change for this transaction
	public boolean fraudDetection; //true if fraud detected, false if no fraud detected. 
	public boolean isStarted=false;
	public boolean isFinished=false;
	
	Item currentItem;
	Customer currentCustomer;
	
	JPanel titlePanel = null;
	JPanel transactionPanel = null;
	JPanel buttonsPanel = null;
	JPanel remindersPanel = null;
	
	JPanel mainPanel = new JPanel();
	
	Dimension d = new Dimension(470,0);
	
	JLabel title = new JLabel("<html><center><u>Welcome to the Self Check-Out <br><br><br></u></center></html>");
	JLabel enterCustNr = new JLabel("<html>Please enter your personal customer number: <br><br></html>");
	String welcomeMessageString = "Hello "+ customerName + "!";
	JLabel welcomeMessage = new JLabel(welcomeMessageString);
	
	String scanItemText2 = "Please scan your item...";
	JLabel scanItemText = new JLabel(scanItemText2);
	
	String scanItemText22 = "Then place it in the bagging area.";
	JLabel scanItemText1 = new JLabel(scanItemText22);

	JTextField customerNrField = new JTextField(5);
	
	JLabel amountTenderedLabel = new JLabel("<html> Enter your amount tendered here: <br><br></html>");
	JButton startShoppingButton = new JButton("START Shopping");
	JButton scanItemButton = new JButton("SCAN item");
	JButton finishAndPayButton = new JButton("Finish and Pay");
	JLabel subTotalLabel = new JLabel();
	JLabel yourShopping = new JLabel("Your Shopping");
	JTextArea transactionDetails = new JTextArea(18,30);
	JTextField enterAmountTendered = new JTextField();
	
	JLabel totalAmountInfo = new JLabel("<html><b><br><br><br>The total amount owed is:  <br> <br> </b></html>");
	JLabel transactionInfo = new JLabel("<html><br><br><u>Your transaction details are :</u><br><br></html>");
	JLabel changeText = new JLabel("<html><center><br><br>Your change is: <br><br><br></center> </html>");
	JLabel thanksText = new JLabel("<html><center>Thank you for shopping at the Self-Check out.<br><br><br>" +
			"Your receipts and recipes will be emailed to you shortly <br> to the following email address: </center> </html>");
	JLabel updateRemindersText = new JLabel("<html><br><br>Please tick those items which you still wish to be reminded about<br><br></html>");
	JLabel remindersThanks = new JLabel("Thank you for updating your reminders list.");
	
	//JTextArea remindersDetails = new JTextArea(25,44);
	JLabel remindersInfo = new JLabel("<html><br><br><u>Your set reminders details are :</u><br><br></html>");
	JLabel remindersSection = new JLabel();//displays the reminders;
	
	ImageIcon icon = new ImageIcon("shopping.jpg");
	JLabel imageLabel = new JLabel();
	
	JButton finalPayButton = new JButton("Pay");
	JButton updateRemindersButton = new JButton("Update Reminders");
	JCheckBox[] reminderChecks = new JCheckBox[9];
	
	JCheckBox item;//for displaying reminders
	public String[] remindersList;
	public String[] updatedRemindersList;
	
    //welcome and customer number
    public JPanel getTitlePanel()
    {
    	titlePanel = new JPanel();
    	titlePanel.setLayout(new BoxLayout(titlePanel, BoxLayout.Y_AXIS));
    	
    	Font titleFont = new Font("Arial", Font.BOLD, 30);
    	title.setFont(titleFont);
    	
    	title.setForeground(Color.blue);
    	titlePanel.add(title);
    	title.setAlignmentX(Component.CENTER_ALIGNMENT);
    	title.setAlignmentY(Component.CENTER_ALIGNMENT);
    	titlePanel.add(Box.createRigidArea(new Dimension(0,5)));
    	
    	Font f = new Font("Arial",Font.BOLD,18);
    	enterCustNr.setFont(f);
    	enterCustNr.setAlignmentX(Component.CENTER_ALIGNMENT);
    	titlePanel.add(enterCustNr);
    	
    	customerNrField.setAlignmentX(Component.CENTER_ALIGNMENT);
    	Dimension size = new Dimension(40,40);
    	customerNrField.setMaximumSize(size);
    	customerNrField.setPreferredSize(size);
    	customerNrField.setMinimumSize(size);
    	titlePanel.add(customerNrField);
    	
    	
    	welcomeMessage.setFont(f);
    	welcomeMessage.setAlignmentX(JComponent.CENTER_ALIGNMENT);
    	welcomeMessage.setAlignmentY(JComponent.CENTER_ALIGNMENT);
    	//titlePanel.add(Box.createHorizontalGlue());
    	titlePanel.add(welcomeMessage);
    	//titlePanel.add(Box.createHorizontalGlue());
    	welcomeMessage.setVisible(false);
    	
    	scanItemText.setFont(f);
    	scanItemText.setAlignmentX(JComponent.CENTER_ALIGNMENT);
    	scanItemText.setAlignmentY(JComponent.CENTER_ALIGNMENT);
    	titlePanel.add(scanItemText);
    	scanItemText.setVisible(false);
    	
    	scanItemText1.setFont(f);
    	scanItemText1.setAlignmentX(JComponent.CENTER_ALIGNMENT);
    	scanItemText1.setAlignmentY(JComponent.CENTER_ALIGNMENT);
    	titlePanel.add(scanItemText1);
    	scanItemText1.setVisible(false);
    	
    	
    	titlePanel.setVisible(true); //this will always be true
    	return titlePanel;
    }
    
    //reminders
    public JPanel getRemindersPanel()
    {
    	JPanel remindersPanel = new JPanel();
    	remindersPanel.setLayout(new BoxLayout(remindersPanel, BoxLayout.Y_AXIS));
    	remindersInfo.setAlignmentX(Component.LEFT_ALIGNMENT);
    	Font font = new Font("Arial", Font.BOLD, 18);
    	remindersInfo.setFont(font);
    	remindersPanel.add(remindersInfo);
    	remindersInfo.setVisible(false);
    	

    	remindersPanel.add(remindersSection);
    	remindersSection.setVisible(false);
    	
    	remindersPanel.add(updateRemindersText);
    	remindersPanel.add(updateRemindersButton);
    	
    	updateRemindersText.setVisible(false);
    	updateRemindersButton.setVisible(false);
    	remindersThanks.setVisible(false);
    	
    	remindersPanel.setVisible(true);
    	return remindersPanel;
    }
    
    public JPanel getTransactionsPanel()
    {
    	transactionPanel = new JPanel();
    	transactionPanel.setLayout(new BoxLayout(transactionPanel, BoxLayout.Y_AXIS));
    	
    	
    	transactionInfo.setAlignmentX(Component.LEFT_ALIGNMENT);
    	//transactionInfo.setAlignmentY(Component.LEFT_ALIGNMENT);
    	Font font = new Font("Arial", Font.BOLD, 18);
    	transactionInfo.setFont(font);
    	transactionPanel.add(transactionInfo);
    	transactionInfo.setVisible(false);
    	
    	Font font1 = new Font("Arial", Font.PLAIN, 15);
    	transactionDetails.setFont(font1);
    	transactionDetails.setAlignmentX(Component.LEFT_ALIGNMENT);
    	transactionDetails.setAlignmentY(Component.LEFT_ALIGNMENT);
    	
    	transactionDetails.setMaximumSize(d);
    	transactionDetails.setPreferredSize(d);
    	transactionDetails.setMinimumSize(d);
    	transactionDetails.setOpaque(false);
    	transactionPanel.add(transactionDetails);
    	//transactionDetails.add(Box.createRigidArea(new Dimension(10, 40)));
    	transactionDetails.setVisible(false);
    
    	
    	//sTotal = main.getCurrentTotal();
    	
    	subTotalLabel.setText("Sub-total: "+subTotal);
    	subTotalLabel.setFont(font);
    	subTotalLabel.setAlignmentX(Component.LEFT_ALIGNMENT);
    	subTotalLabel.setAlignmentY(Component.LEFT_ALIGNMENT);
    	transactionPanel.add(subTotalLabel);
    	subTotalLabel.setVisible(false);

    	//imageLabel.setIcon(icon);
    	//transactionPanel.add(imageLabel);
    	//imageLabel.setVisible(true); 
    	
    	
    	
    	totalAmountInfo.setFont(font);
    	totalAmountInfo.setAlignmentX(Component.LEFT_ALIGNMENT);
    	totalAmountInfo.setAlignmentY(Component.LEFT_ALIGNMENT);
    	transactionPanel.add(totalAmountInfo);
    	totalAmountInfo.setVisible(false);
    	
    	amountTenderedLabel.setAlignmentX(Component.LEFT_ALIGNMENT);
    	amountTenderedLabel.setFont(font);
    	transactionPanel.add(amountTenderedLabel);
    	amountTenderedLabel.setVisible(false);
     	
    	Dimension d = new Dimension(100,50);
    	enterAmountTendered.setMaximumSize(d);
    	enterAmountTendered.setPreferredSize(d);
    	enterAmountTendered.setMinimumSize(d);
    	enterAmountTendered.setAlignmentX(Component.LEFT_ALIGNMENT);
    	transactionPanel.add(enterAmountTendered);
    	enterAmountTendered.setVisible(false);
    	enterAmountTendered.add(Box.createRigidArea(new Dimension(100, 50)));
    	
    	finalPayButton.setAlignmentX(Component.LEFT_ALIGNMENT);
    	transactionPanel.add(finalPayButton);
    	finalPayButton.addActionListener(this);
    	finalPayButton.setVisible(false);
    	
    
    	transactionPanel.add(changeText);
    	changeText.setFont(font);
    	//changeText.add(Box.createRigidArea(new Dimension(10, 20)));
    	changeText.setVisible(false);
    
    	thanksText.setFont(font);
    	transactionPanel.add(thanksText);
    	thanksText.setVisible(false);
 
    	transactionPanel.setVisible(true);
    	
    	return transactionPanel;
    }
    
    //buttons
    public JPanel getButtonsPanel()
    {
    	buttonsPanel = new JPanel();
    	buttonsPanel.setLayout(new BoxLayout(buttonsPanel, BoxLayout.Y_AXIS));
    	buttonsPanel.add(Box.createRigidArea(new Dimension(10, 50)));
    	
    	buttonsPanel.add(scanItemButton);
    	scanItemButton.setAlignmentX(Component.CENTER_ALIGNMENT);
    	//scanItemButton.setAlignmentY(Component.CENTER_ALIGNMENT);
    	buttonsPanel.add(Box.createRigidArea(new Dimension(10, 50)));
    	scanItemButton.addActionListener(this);
    	scanItemButton.setVisible(false);
    	
    	finishAndPayButton.setAlignmentX(Component.CENTER_ALIGNMENT);
    	//inishAndPayButton.setAlignmentY(Component.CENTER_ALIGNMENT);
    	buttonsPanel.add(Box.createRigidArea(new Dimension(10, 50)));
    	buttonsPanel.add(finishAndPayButton);
    	finishAndPayButton.addActionListener(this);
    	finishAndPayButton.setVisible(false);
    
    	startShoppingButton.setAlignmentX(Component.CENTER_ALIGNMENT);
    	//startShoppingButton.setAlignmentY(Component.CENTER_ALIGNMENT);
    	startShoppingButton.addActionListener(this);
    	buttonsPanel.add(startShoppingButton);
    	startShoppingButton.setVisible(true);
    
    	return buttonsPanel;
    }
    
    
    public void actionPerformed(ActionEvent e)
    {   
    	if (e.getSource() == scanItemButton)
    		scanItem();
        else if (e.getSource() == finishAndPayButton)
        	finishAndPay();
        else if (e.getSource() == startShoppingButton)
        	startShopping();
        else if (e.getSource()== finalPayButton)
        	finalScreen();
        else if (e.getSource()== updateRemindersButton)   	
        	getUpdatedReminders();
    }
    
    public String[] getUpdatedReminders() 
    {
    	remindersThanks.setVisible(true);
    	return updatedRemindersList;
    }
    
    public void startShopping()
    {
    	isStarted=true;
    
    	
    	//in title panel...
    	welcomeMessage.setVisible(true);
    	scanItemText.setVisible(true);
    	scanItemText1.setVisible(true);
    	enterCustNr.setVisible(false);
    	customerNrField.setVisible(false);
    	
    	/**
    	//add reminders to the panel
    	for(int i=0; i<remindersList.length;i++)
    	{
    		reminderChecks[i] = new JCheckBox(remindersList[i]);
    		remindersSection.add(reminderChecks[i]);
    		reminderChecks[i].addActionListener(this);
			
    	}*/
    	
    	//in buttons panel
    	startShoppingButton.setVisible(false);
    	scanItemButton.setVisible(true);
    	finishAndPayButton.setVisible(true);
    	
    	//in transactions panel
    	transactionInfo.setVisible(true);
    	transactionDetails.setVisible(true);
    	subTotalLabel.setVisible(true);
    	//subTotalLabel.setVisible(true);
    	//in reminders panel
    	remindersInfo.setVisible(true);
    	remindersSection.setVisible(true);
    	updateRemindersText.setVisible(true);
    	updateRemindersButton.setVisible(true);

    	
    }
    
    public void test2(String s)
    {
    	transactionDetails.repaint();
    	transactionDetails.append(s +"\t\n");
    	transactionDetails.updateUI();

    	transactionPanel.repaint();
    }
    
    
    public void scanItem()
    {	
    	//itemName = currentItem.name();
    	//itemPrice = currentItem.price();
    	//itemAllergies = currentItem.allergy();
    	
    	
    	
    	
    	transactionDetails.append(itemName +"\t");
    	transactionDetails.append("€"+ itemPrice +"\t");
    	transactionDetails.append(itemAllergies +"\n");
    	//subTotal = getCurrentTotal();
    	
    	 
    }
    
    public void finishAndPay()
    {
    	welcomeMessage.setVisible(true);
    	scanItemText.setVisible(false);
    	scanItemText1.setVisible(false);
    	transactionInfo.setVisible(false);
    	transactionDetails.setVisible(false);
    	subTotalLabel.setVisible(false);
    	scanItemButton.setVisible(false);
    	finishAndPayButton.setVisible(false);
    	
    	totalAmountInfo.setVisible(true);
    	amountTenderedLabel.setVisible(true);
    	enterAmountTendered.setVisible(true);
    	finalPayButton.setVisible(true);
    } 
    
    public void finalScreen()
    {
    	isFinished=true;
    	totalAmountInfo.setVisible(false);
    	amountTenderedLabel.setVisible(false);
    	enterAmountTendered.setVisible(false);
    	finalPayButton.setVisible(false);
    	remindersInfo.setVisible(false);
    	remindersSection.setVisible(false);
    	remindersInfo.setVisible(false);
    	updateRemindersText.setVisible(false);
    	updateRemindersButton.setVisible(false);
    	remindersThanks.setVisible(false);
    	
    	thanksText.setVisible(true);
    	changeText.setVisible(true);
    	
    	
    	changeText.setAlignmentX(Component.CENTER_ALIGNMENT);
    	transactionPanel.add(changeText);
    	thanksText.setAlignmentX(Component.CENTER_ALIGNMENT);
    	transactionPanel.add(thanksText);
    }
}


