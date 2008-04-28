//package selfCheckOut.userInterface;
//package ui;

/**
 * @author Grainne Mulligan
 * */



import java.awt.Color;
import java.awt.GridLayout;

import javax.swing.JFrame;
//import javax.swing.UIManager;
//import javax.swing.UnsupportedLookAndFeelException;
//import selfCheckOut.SelfCheckOut;

public class Ui
{
	static final long serialVersionUID=0;
	//Interface i=null;
	//Interface i=null;
    
	
	SelfCheckOut theCaller = null;
	
	
	public Interface i= null;
	 public  Ui(SelfCheckOut theCaller) {
		 
		 i= new Interface(theCaller);
		 
		 this.theCaller = theCaller;
		 
	    	//i.setSize(1100,900);
	    	i.setSize(1000,750);
	    	i.setResizable(false);
	    	i.setBackground(Color.YELLOW);
	        i.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
	    	i.setLayout(new GridLayout(2,2));
	    	i.add(i.getTitlePanel());
	    	i.add(i.getTransactionsPanel());
	    	i.add(i.getButtonsPanel());
	    	i.add(i.getRemindersPanel());
	        i.setVisible(true);
	        //getReminders();
	        //i.customerName=currentCustomer.myName();
	        
	        //ItemQuery currentItem = new ItemQuery();
	        //i.itemName=currentItem.name;
	       // i.itemPrice=currentItem.price;
	        //i.itemAllergies=currentItem.allergy;
	        
	 }
	 
	 
	   public void displayItems(ItemQuery currentItem) {
           i.displayItems(currentItem);
       }

	 public void write(String ss) {
		 
		 i.test2(ss);
		 
	 }

}
