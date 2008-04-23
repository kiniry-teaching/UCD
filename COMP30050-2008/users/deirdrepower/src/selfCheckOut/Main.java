package selfCheckOut;
import database.createCustomer;
import database.getCustomer;
import database.ItemQuery;
import database.Product;
import database.Query;
import selfCheckOut.USI.*;
import selfCheckOut.hardWareInterface.*;
import selfCheckOut.hardwareStuff.*;

import java.awt.*;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import javax.sound.sampled.LineUnavailableException;
import selfCheckOut.USI.*;
/**@author deirdrepower
 * */


public class Main extends Thread {
	//private Barcode barcode;
	//private static double amountOwed;
	private static double amountTendered;
	private static double currentTotal;
	private static double change;
	//private String itemname;
	//private double priceA;
	//private double lThresholdA;
	//private double hThresholdA;
	//private String sFileNameA;
	//private int alergyInfoA;
	//private boolean primeItemA;
	private static Product aProduct;;
	private static HWIconduit hwc = null;
	private static String customerName;
	private static boolean checkingfraud;
	//	while loop check isfinished !=true

	public static void main(String[] args) throws IOException {
	System.out.println("Enter something");
	BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
	String aname = null;
	//String number = null;
	try{
		aname = br.readLine();
		
	}
	catch(IOException ioe){
		System.out.println("IOError");
		System.exit(1);
	}
	System.out.println("success!!!");
	System.out.println(aname);
	
	System.out.println("Enter something else");
	BufferedReader breader = new BufferedReader(new InputStreamReader(System.in));
	//String aname = null;
	String number = null;
	try{
		number = breader.readLine();
		
	}
	catch(IOException ioe){
		System.out.println("IOError");
		System.exit(1);
	}
	System.out.println("success!!!");
	System.out.println(aname);
	
	
	currentTotal = 0;
	amountTendered =0;
	
while(InfoSenderReceiver.isStarted() == true)
	{
		
		int CustomerNumber = InfoSenderReceiver.getCustomerNr();//gets the customer number from the UI
		Customer aCustomer = getCustomer(CustomerNumber);//gets the customer name from the database
    	InfoSenderReceiver.getCustomerName(aCustomer);//sends this name to the UI
		hwc = new HWIconduit();//	creates a new hardware emulator
		hwc.start();//	starts the hardware emulator
		int counter = 0;
		while (true) {
			counter++;
			//	am going to have to get the initial weights here
				
			HardWareResult aResult = null;//creates a new hardwareresult
			aResult = hwc.getHardWareResult();//gets the hardwareresult 
				VoiceAnnouncer.playBeep();//plays the beep
				checkingfraud =  ItemValidator.itemvalidator(aResult);
				if(checkingfraud == true){
					InfoSenderReceiver.checkFraud(checkingfraud);
					aProduct = ItemValidator.getItem();
					currentTotal = PriceCalculator.calculatePrice(currentTotal, aProduct);
					InfoSenderReceiver.getCurrentTotal(currentTotal);
					InfoSenderReceiver.getProduct(aProduct);
					Receipt.addItem(aProduct);
					Transaction.addItem(aProduct);
				}
				else{
					InfoSenderReceiver.checkFraud(checkingfraud);
				}
				
					
			}
			if (counter == 50) {
				System.out.print(".");
				hwc.gather(true);
				counter = 0;
			}
			try {
				sleep(200);
			} catch (InterruptedException e) {
				System.out.println("selfCheckOut() exception = " + e.toString());
				e.printStackTrace();
			}	
			

			
		}
		InfoSenderReceiver.getTotalPrice(currentTotal);
		amountTendered = InfoSenderReceiver.getAmountTendererd();
		change = ChangeGenerator.generateChange(currentTotal, amountTendered);
		InfoSenderReceiver.getChange(change);
	}}
	
