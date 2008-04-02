/**
 * 
 * @author  patrick Nevin: 06754155
 * @created 02/04/08 version 0.1
 */

public class Input_handler 
{
	/**
	 * @return What are the legal keyboard inputs?,
	 * Is this character a legal keyboard input
	 * @requires true
	 * @assert false
	 */	
	private boolean is_legal(char ch)
	{
		//N.B. need to inculde char for shift....
		char[] legal_inputs = {'h', 'm', ' ', '\u001B', '\r','a','s'};
		for(int i = 0; i <= legal_inputs.length; i++) 
		{
			if (legal_inputs[i] == ch)
				return true;
		}
		return false;
	}
	/**
	 * 
	 *
	 */
	private void process_char(char ch) 
	{
		switch (ch) 
		{  'h', 'm', ' ', '\u001B', '\r','a','s'
			case 'h': ; break;
			case 'm': new Turn_left(); break;
			case 'h': new Turn_left(); break;
			case 'h': new Turn_left(); break;
		}
	}
/**
 * 
 	  command
 	    "Process this keyboard input character."
 	  constraint
 	    "One can only start the game while the high score list is being shown.",
 	    "Asking for the high score list only works during the game demo.",
 	    "Player input only works while the game is being played."
 */
}
