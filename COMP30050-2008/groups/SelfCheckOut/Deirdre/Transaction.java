package selfCheckOut;
/*@author deirdre power
 * */
import java.util.Date;
import java.util.LinkedList;
import database.Item;
public class Transaction {

	private static LinkedList<Item> itemList = new LinkedList<Item>();
	private static Date datetime;
	public Transaction(){
		datetime = new Date();
	}
	
	public static void addItem(Item anItem){
		itemList.add(anItem);
		
	}
	
	public static int numberItem(){
		return itemList.size();
		 
	}
	
	public static Date getDate(){
		return datetime;
	}
	
	public static LinkedList<Item> getList(){ 
		return itemList;
	}
	
}
