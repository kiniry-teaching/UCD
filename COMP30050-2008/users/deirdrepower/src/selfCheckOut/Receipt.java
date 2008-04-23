package selfCheckOut;
/*@author deirdre power
 * **/
import java.util.Date;
import java.util.LinkedList;
import database.Product;
public class Receipt {
	//change product to item
	private static LinkedList<Product> itemList = new LinkedList<Product>();
	private static Date datetime;
	
	public Receipt(){
		
	}

	
	
	public static void addItem(Product anItem){
		itemList.add(anItem);
		
	}
	
	public static int numberItem(){
		return itemList.size();
		 
	}
	
	public static Date getDate(){
		return datetime;
	}
	
	public static LinkedList<Product> getItemlist(){
		return itemList;
	}

}
