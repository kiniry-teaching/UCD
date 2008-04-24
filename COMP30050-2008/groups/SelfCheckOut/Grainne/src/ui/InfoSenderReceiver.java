package ui;

//import database.Item;
//import database.Customer;
import javax.swing.*;

public class InfoSenderReceiver extends Interface
{
	static final long serialVersionUID=0;
	
	

	/**gets the customer number to send to the main method*/
	public int getCustomerNr()
	{
		return customerNr; 
	}
	
	public void getCustomer(Customer c)
	{
		currentCustomer=c;
	}
	

	
	//gets the item information from the main method, of item just scanned
	//interacts with main method
	public void getItem(Item i)
	{
		currentItem=i;
		
	}

	
	//Provides a running total to be displayed on the UI
	public double getCurrentTotal(double cTotal)
	{	
			subTotal=cTotal;
			return subTotal;
		
		
	}
	
	/**interacts with main method, and returns the total owed by the customer to the UI*/
	public void getTotalPrice(double totalP)
	{
		total=totalP;
		
		
	}

	/**returns the amount tendered, which is entered by the customer via the UI*/
	public double getAmountTendererd()
	{
	
		return amountTendered;
	}
	
	/**interacts with the main method, and returns the change for the transaction*/
	public void getChange(double c)
	{
		change=c;	
	}
	
	
	
	/**interacts with the main method, which signals to the UI true if there is a fraud detected, false otherwise.*/ 
	public void checkFraud()
	{
		
		if(fraudDetection==false)
			JOptionPane.showMessageDialog(null,"WARNING: item not recognised. Please rescan...");		
			
	}

}