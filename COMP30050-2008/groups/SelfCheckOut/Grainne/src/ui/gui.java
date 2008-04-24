package ui;

import java.awt.Color;
import java.awt.GridLayout;

import javax.swing.JFrame;
import javax.swing.UIManager;
import javax.swing.UnsupportedLookAndFeelException;

public class gui
{
	static final long serialVersionUID=0;
	
	 private static void createAndShowGUI() 
	    {
		 
	    	Interface i = new Interface();
	    
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
	        
	        //ItemQuery currentItem = new ItemQuery();
	        i.itemName=currentItem.name;
	        i.itemPrice=currentItem.price;
	        i.itemAllergies=currentItem.allergy;
	        
	        try 
      	  	{ // Poll every ~10 ms
                Thread.sleep(50);
                
            }
      	  
            catch (InterruptedException e) {}
            
	        
	        /**
	        for(int j=0;j<10000;j++)
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
	        }*/
	        
	    }
	    
	    public static void main(String[] args) 
	    {
	    	//public void run() 
            //{
                createAndShowGUI();
            //}
	    	
	    	
	    	
	    	
	    	/**
	  
	        try {
	            UIManager.setLookAndFeel("javax.swing.plaf.metal.MetalLookAndFeel");
	        } catch (UnsupportedLookAndFeelException ex) {
	            ex.printStackTrace();
	        } catch (IllegalAccessException ex) {
	            ex.printStackTrace();
	        } catch (InstantiationException ex) {
	            ex.printStackTrace();
	        } catch (ClassNotFoundException ex) {
	            ex.printStackTrace();
	        }
	       
	        UIManager.put("swing.boldMetal", Boolean.FALSE);
	        
	        //Schedule a job for the event dispatch thread:
	        //creating and showing this application's GUI.
	        javax.swing.SwingUtilities.invokeLater(new Runnable() 
	        {
	        	
	        	
	            public void run() 
	            {
	                createAndShowGUI();
	            }
	        });
	    }    
	    */	
	    }

}
