package selfCheckOut;
/*@author deirdre power
 * **/
import java.util.Date;
import java.util.LinkedList;
import selfCheckOut.dataBase.*;
public class Receipt {
	//change product to item
	private static LinkedList<ItemQuery> itemList = new LinkedList<ItemQuery>();
	private static Date datetime;
	
	public Receipt(){
		
	}
	
	public static void addItem(ItemQuery anItem){
		itemList.add(anItem);
	}
	
	public static int numberItem(){
		return itemList.size();
	}
	
	public static Date getDate(){
		return datetime;
	}
	
	public static LinkedList<ItemQuery> getItemlist(){
		return itemList;
	}

}
