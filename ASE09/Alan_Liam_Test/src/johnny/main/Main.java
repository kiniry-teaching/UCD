package johnny.main;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import johnny.JohnnyBank;
import johnny.JohnnyCard;
import johnny.JohnnyMachine;
import johnny.JohnnyRegister;

public final class Main {

	  public JohnnyBank bank;
	  public JohnnyMachine machine;
	  public JohnnyCard card;
	  public JohnnyRegister register;
	  public final static char PULL = 'p';
	  public final static char REMOVE = 'r';
	  public final static char ADD = 'a';
	  public final static char TERMINAL = 't';
	  public final static char REGISTER = 'r';
	  public final static char QUIT = 'q';
	  private Main() {
		  this.initialize() ;
	  }

	  /** Initialize the Johnny Card system. */
	  private void initialize() {

	    // Create a new JOHHNY_BANK.
	    bank = new JohnnyBank(0,new int[]{1, 2, 3, 4});
		// Create a new JOHNNY_TERMINAL.
	    machine = new JohnnyMachine(new JohnnyBank[]{bank});
	    // Create a new JOHHNY_REGISTER.
	    register = new JohnnyRegister();
	    // Create a new JOHNNY_CARD.
	    //Reference to card is stored in the bank
	    bank.addCard() ;
	    bank.updateBankBalance(-100) ;
	    card = bank.getCards()[0] ;
	    
	  }
	  public char readChoice(){
		    BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
		    //Set default to null character
		    char input = '\0';
			try {
				input = (char)br.read();
			} catch (IOException e) {
				e.printStackTrace();
			}
			
			return Character.toLowerCase(input) ;
	  }
	  public int readInt(){
		    BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
		    int input = 0;
			try {
				String temp = br.readLine() ;
				input = Integer.parseInt(temp) ;
			} catch (IOException e) {
				e.printStackTrace();
			} catch(NumberFormatException e){
				input = -1 ;
			}
			return input ; 
	  }
	  /** @return What does the user want to do with their card? */
	  //@ ensures \result <==> (* User decided to put their card in the terminal. *); 
	  boolean cardInTerminal() {
		boolean decision = true ;
	    // Tell the user that they can either insert their card into a terminal
	    this.tellUser("Hello, you can insert your card into a Terminal or Register") ;
	    // 't' or a register 'r'.
	    this.tellUser("Type \'t\' for Terminal to add cash or \'r\' for Register to spend cash") ;
	    // Ask the user what they want to do.
	    // Return the user's decision.

	    char input = 't';
	    
	    input = readChoice() ;
	    
	    if(Main.REGISTER == input){
	    	decision = false ;
	    }
	    return decision ;
	  }

	  /** Tell the user something. */
	  private void tellUser(/*@ non_null @*/ String message) {
	    // Send a string to the console.
	    System.out.println(message);
	  }
	  
	  /**
	   * Runs an interactive loop exercising a demonstration
	   * Johnny Card system.
	   *
	   * @param the_args the arguments of the program.
	   */
	  public static void main(final /*@ non_null @*/ String[] the_args) {
	    // Initialize the Johnny Card system.
	    Main app = new Main() ;
	    char input = '1' ;
		// Tell the user that they have an empty card.
	    app.tellUser("Your card is empty") ;
	    // LOOP
	    do{
	    	// What does the user want to do with their card?
		    if(app.cardInTerminal()){
			    //   TERMINAL:
			    //   LOOP
		    	app.machine.acceptCard(app.card) ;
		    	do{
		    		app.tellUser("Please enter your pin numer: ") ;
		    		int[] pin = new int[JohnnyBank.PIN_LENGTH] ;
		    		for(int i = 0; i < JohnnyBank.PIN_LENGTH; i++){
		    			pin[i] = app.readInt() ;
		    		}
		    		app.machine.checkPin(pin) ;
		    	}while(!app.machine.isAccepted() && !app.card.isLocked()) ;
		    	// Tell the user their balance.
	    		app.tellUser("Your balance is: "+app.bank.getBankBalance()) ;
			    do{	
			    	if(app.machine.isAccepted()){
				    	// Ask the user if they wish to add or remove cash from the card, or pull their card out.
				    	app.tellUser("How much cash would you like to add or remove(coming soon) from your card? A:R:P") ;
				    	input = app.readChoice() ;
				    	if(Main.ADD == input){
					    	// ADD:
					    	//   Ask the user how much they wish to add.
					    	app.tellUser("How much would you like to add to your card? ") ;
					    	//   Add that value to the card (if possible).
					    	int amount = app.readInt() ;
					    	app.machine.ammountOfCashToPutOnCard(amount) ;
					    		
				    	}else if(Main.REMOVE == input){
				    		// REMOVE:
				    		//   Ask the user how much they wish to remove.
				    		//   Remove that value to the card (if possible).
				    		app.tellUser("Remove funds from card is not yet supported, Coming Soon!") ;
				    	}else if(Main.PULL == input){
				    		// PULL:
				    		//   Tell the user their new balance.
				    		app.tellUser("Your balance is now: "+app.bank.getBankBalance()) ;	
				    	}else{
				    		app.tellUser("Sorry that option is not available") ;
				   		}
			    	}
			   	}while(Main.PULL != input && !app.card.isLocked());
		    }else{
			    //   REGISTER:
			    app.register.acceptCard(app.card) ;
			    //   Does the user accept a sale of value 1?
			    app.tellUser("Do you want to make a sale of 1? y or n") ;
			    char tempInput = app.readChoice() ;
			    if('y' == tempInput){
			    	app.register.transferCash(1) ;
			    }
		    }
		    app.tellUser("Quit ? (q/c):") ;
		    input = app.readChoice() ;
	    }while(Main.QUIT != input);
	    
	    return;
	  }
	}

