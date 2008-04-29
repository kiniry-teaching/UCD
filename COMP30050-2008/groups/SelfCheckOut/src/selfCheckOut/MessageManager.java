package selfCheckOut;

import java.awt.List;
import selfCheckOut.userInterface.*;
import selfCheckOut.dataBase.*;

/**
 * @author deirdrepower
 * */
public class MessageManager {
	private static String[] reminders;
	//public static List alist = null;
	
	public static String[] getUserList(int number){
	//	reminders = database.getReminder.getReminders(number);
		
		//its an array!!! Not a list 
		//List reminders = new List<Item>;
		/*TODO: Implement code to retrieve the list of items for the user*/
		
		return reminders;

	}
	public static void editedUserList(){
		//InfoSenderReceiver.
		//qreturn reminders;
	/*TODO: Implement code to edit this list depending on what the user wants to edit*/
	}
	
	public static String[] sendUserListDB(){
		return reminders;
		/*TODO: Implement code to send the user list to the Database*/
	}
 }



