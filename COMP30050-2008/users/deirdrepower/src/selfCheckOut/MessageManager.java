package selfCheckOut;
import java.awt.List;

/**
 * @author deirdrepower
 * */
public class MessageManager {
	
	public static List alist = null;
	
	public static List getUserList(int number){
		//its an array!!! Not a list 
		//List reminders = new List<Item>;
		/*TODO: Implement code to retrieve the list of items for the user*/
		
		return alist;

	}
	
	public static List sendUserListUI(){
		return alist;
		
	/*TODO: Implement code to send this list to the user*/
	}
	
	public static List editedUserList(){
		return alist;
	/*TODO: Implement code to edit this list depending on what the user wants to edit*/
	}
	
	public static List sendUserListDB(){
		return alist;
		/*TODO: Implement code to send the user list to the Database*/
	}
	
 }
