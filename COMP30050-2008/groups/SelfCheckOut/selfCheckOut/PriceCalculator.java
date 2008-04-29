package selfCheckOut;

import selfCheckOut.userInterface.*;
import selfCheckOut.dataBase.*;
/**@author deirdrepower
 * */

//this class returns the overall price owed by the customer
public class PriceCalculator {
	

		public static double calculatePrice(double overallPrice, ItemQuery aProduct){
			double itemPrice = aProduct.price;
			double newOverallPrice;
			newOverallPrice = overallPrice + itemPrice;
			double roundPrice = Math.round(newOverallPrice*100.0)/100.0;
			System.out.println("Old price");
			return roundPrice;
			
			
		}
		
		public static double checkprice(double overallPrice, double itemPrice){
			double newOverallPrice;
			newOverallPrice = ((overallPrice*100)+(itemPrice*100))/100;
			double roundPrice = Math.round(newOverallPrice*100.0)/100.0;
			System.out.println("new price");
			return roundPrice;
		}
}

