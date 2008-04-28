package ui;

import java.awt.Color;
import java.awt.GridLayout;
import javax.swing.JFrame;

public class Ui
{
	static final long serialVersionUID=0;
	Interface i=null;
    
	 private static void createAndShowGUI() 
	    {
		 	
	    	
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
	        i.customerName=currentCustomer.myName();
	        
	        ItemQuery currentItem = new ItemQuery();
	        i.itemName=currentItem.name;
	        i.itemPrice=currentItem.price;
	        i.itemAllergies=currentItem.allergy;
	        
	        try 
      	  	{ // Poll every ~10 ms
                Thread.sleep(50);
                
            }
      	  
            catch (InterruptedException e) {}
            
	        
	        
	        for(int j=0;j<10;j++)
	        {
	        	String ss = "";
	        	ss=ss+j;
	        	i.test2(ss);
	        	System.out.print(j);
	        	  try 
	        	  { // Poll every ~10 ms
	                  Thread.sleep(50);
	                  
	              }
	        	  
	              catch (InterruptedException e) {}
	              //appendToChatBox("INCOMING: " + "\n");
	        }
	      
	        
	    }
	    
	    public static void main(String[] args) 
	    {
	    	//public void run() 
            //{
	    		i= new Interface();
                createAndShowGUI();
            //}
	    	
	    
	    }

}
