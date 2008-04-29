package selfCheckOut;
import selfCheckOut.hardWareInterface.*;
import selfCheckOut.dataBase.ItemQuery;

/**@author deirdrepower
 * */
public class ItemValidator {
	private static int lowert;
	private static int highert;
	private static int lastweightNCO;
	private static int lastweightCO;
	private static int currentweightNCO;
	private static int currentweightCO;
	private static ItemQuery aProduct;
	private static long timestampW1;
	private static long timestampW2;
	private static long timestampbarcode;
	private static boolean formatch = false;
	private static boolean checkinitialweight = false;
	private static boolean forcheckfraud = false;
	private static boolean foritemvalidator = false;
	private static boolean isvalidobject = false;
	private static int counter = 0;
	//carries out the item validator procedure and returns true of false depending on the validation
	public static boolean itemvalidator(HardWareResult aResult){
		
	getHardwareWeights(aResult);//stores the weights and time stamps from the hardwareResult object
	BarCode[] thebarcodes = aResult.getBarCodes();//stores the BarCodes from the hardwareResult object
		//System.out.println("the weight"+currentweightNCO);
		//System.out.println("the weight"+currentweightCO);
		//System.out.println("the timestamp"+timestampW1);
		//System.out.println("the timestamp"+timestampW2);
		while(foritemvalidator ==false || thebarcodes.length != counter){	
		for(int i = 0; i<thebarcodes.length; i++)
			{	
				counter ++;
				getBarcodetimeStamp(thebarcodes[i]);
				getItemDetails(thebarcodes[i]);
				isMatch();
				if(formatch == false)
					{
						foritemvalidator = false;
					}
				else{
					getItemDetails(thebarcodes[i]);
					if(isvalidobject == false)
					{
						weightCheck();
						if(forcheckfraud == false)
						{
							foritemvalidator = false;
						}
						else{
							foritemvalidator = true;
							lastweightNCO = currentweightNCO;
							lastweightCO = currentweightCO;
						}
					}
				}

			}
	}
		return foritemvalidator;

	}
	
	//gets the initial weights of the scales before the transaction begins and ensures that 
	//they are valid weights for the initial set!!
	public static boolean getInitialWeight(HardWareResult aResult){
		Weight weightA = aResult.getWeight(0);
		Weight weightB = aResult.getWeight(1);
		
		lastweightNCO = weightA.getWeightInt();
		lastweightCO = weightB.getWeightInt();
		if(lastweightCO != 0 || lastweightNCO == 0)
		{
			checkinitialweight = false;
		}
		else
		{
			checkinitialweight = true;
		}
		return checkinitialweight;
		
	}
	
	//gets and stores the time stamp for the BarCode
	public static void getBarcodetimeStamp(BarCode aBarcode)
	{
		timestampbarcode = aBarcode.getTimeStamp();
	}
	
	//gets the weights from the hardware object and stores them and their time stamps
	public static void getHardwareWeights(HardWareResult aResult){
		Weight aWeight1 = aResult.getWeight(0);
		Weight aWeight2 = aResult.getWeight(1);
		timestampW1 = aWeight1.getTimeStamp();
		timestampW2 = aWeight2.getTimeStamp();
		
		currentweightCO = aWeight1.getWeightInt();
		currentweightNCO = aWeight2.getWeightInt();
	}
	//sends item details to the database which returns the item
	public static boolean getItemDetails(BarCode aBarcode){
	
			ItemQuery aProduct =new ItemQuery(aBarcode);//this is correct code elsewhere has to be changed GETS the product from the database
			if(aProduct.name == null)//if product for that BarCode exists does not exist
			{
				isvalidobject = false;
			}
			else{
				isvalidobject = true;
				lowert = aProduct.minweight;//store the products thresholds
				highert = aProduct.maxweight;
				
			}
			return isvalidobject;
	}
	
	//checks that the time stamps match. sets the boolean value formatch to true or false
	public static void isMatch(){
		//allow threshold of 60 for the timestamps
			long threstimestamp1high = timestampW1 +60;
			long threstimestamp1low = timestampW1 -60;
			if(timestampW2  <= threstimestamp1high && timestampW2 >= threstimestamp1low)
			{
				if(timestampbarcode  <= threstimestamp1high && timestampbarcode >= threstimestamp1low)
				{
					formatch = true;
				}
			}
			formatch = false;
		}

	public static ItemQuery getItem()
	{
		return aProduct;
	}
	
	//stores the weights and the time stamps from the HardWareResult object
	public static void getWeights(HardWareResult aResult){
			Weight weightA;
			Weight weightB;
			weightA = aResult.getWeight(0);
			currentweightNCO = weightA.getWeightInt();
			timestampW1 = aResult.getWeight(0).getTimeStamp();
			weightB = aResult.getWeight(1);
			currentweightCO = weightB.getWeightInt();
			 timestampW2 = aResult.getWeight(1).getTimeStamp();
	}
	//checks that the weights are valid
	public static boolean weightCheck(){
	
		int wdiffNCO = lastweightNCO - currentweightNCO;//stores the weight difference from the notcheckedout side
		int wdiffCO =  currentweightCO - lastweightCO; //stores the weight difference from the checkedout side
		int lowertCO = wdiffCO - 2;//stores the difference of the checked out side - two to give a lower threshold
		int highertCO =	 wdiffCO + 2;//stores the difference of the checked out side plus two to give a higher threshold
		
		if(wdiffNCO <= highertCO && wdiffNCO >= lowertCO)//checks that the notcheckedoutside weight difference is within the threshold of the checked out side
		{
			if(wdiffNCO >=  lowert && wdiffNCO <= highert)//checks that the weight difference on the notcheckedout side is within the threshold for the product 
			{
				return true;
				
			}
		}
		return false;
	}
}
