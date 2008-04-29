package selfCheckOut;
import java.util.Random;
/**@author deirdre power
 * */
public class ChangeGenerator {
	 
	
	/*What this method does is it generates the change owed to the customer*/
	public static double generateChange(double amountOwed, double amountTendered){
		double change1;
		double change2;
		double roundPrice;
		change1 = amountTendered - amountOwed;
		if(change1 == 0)
		{
			return 0;
		}
		else{
			
			if(isChange(change1) == true)
			{
				double randomEuro = Random();
				change2 = change1+randomEuro;
				roundPrice = Math.round(change2*100.0)/100.0;
				return roundPrice;
				
			}
			else{
				roundPrice = Math.round(change1*100.0)/100.0;
				return roundPrice;
				
			}
			
		}
		
	}
	
	//determines whether change is rounded off to euro or not
	public static boolean isChange(double change)	{

		int ivalue = (int)change;
		double dvalue = (double)ivalue;
		double result = dvalue - ivalue;
		if(result == 0.00){
			return true;
		}
		else{
			return false;
		}
		
	}

	
	//randomly returns 1 or 0
	public static double Random(){
		Random euro = new Random();
		int randomEuro = euro.nextInt(2);
		return randomEuro;
	}
}

