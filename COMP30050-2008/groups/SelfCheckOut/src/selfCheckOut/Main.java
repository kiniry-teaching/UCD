package selfCheckOut;
import selfCheckOut.dataBase.*;
//import database.Item;
//import database.createCustomer;
//import database.getCustomer;
//import database.ItemQuery;
//import database.Query;
//import selfCheckOut.USI.*;
//import selfCheckOut.hardWareInterface.*;
//import selfCheckOut.hardwareStuff.*;

import java.awt.*;

import selfCheckOut.hardWareInterface.HWIconduit;
import selfCheckOut.userInterface.*;
import selfCheckOut.hardWareInterface.HardWareResult;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import javax.sound.sampled.LineUnavailableException;
/**@author deirdrepower
 **/


public class Main extends Thread {
	private static String ipaddress;
	private static double amountTendered = 0;
	private static double currentTotal = 0;
	private static double change = 0;
	private static HardWareResult aResult = null;
	private static ItemQuery aProduct;
	private static HWIconduit hwc = null;
	private static boolean checkingfraud;
	private static HardWareResult initials;
	private static boolean initialsboolean;
	private static int customerNumber;


	public static void main(String[] args) throws IOException {
		System.out.println("Enter IPAddress:");
		BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
		try{
			ipaddress = br.readLine();
			
		}
		catch(IOException ioe){
			System.out.println("IOError");
			System.exit(1);
		}
		System.out.println("success!!!");
		System.out.println(ipaddress);
		
		
	if(InfoSenderReceiver.isStarted() == false)
	{
		sleep(50);
	}
	else{
		while(InfoSenderReceiver.isStarted() == true)
		{
			customerNumber = InfoSenderReceiver.getCustomerNr();
			
			//pass in the customers id
			getCustomer myCustomer = new getCustomer(customerNumber);
			InfoSenderReceiver.getCustomerName(myCustomer);
			
		
			
	
		
	
		hwc.start();//	starts the hardware emulator
		int counter = 0;
		while (true) {
			counter++;
			//getting the first bit in!!!!
			initials = hwc.getHardWareResult();
			initialsboolean = ItemValidator.getInitialWeight(initials);
			if(initialsboolean == false)
			{
				InfoSenderReceiver.checkFraud(initialsboolean);
			}
			
			else{
			aResult = hwc.getHardWareResult();
			VoiceAnnouncer.playBeep();
			checkingfraud = ItemValidator.itemvalidator(aResult);
			if(checkingfraud == true)
			{
				InfoSenderReceiver.checkFraud(checkingfraud);
				aProduct = ItemValidator.getItem();
				VoiceAnnouncer.VoicePlayer(aProduct);
				currentTotal = PriceCalculator.calculatePrice(currentTotal, aProduct);
				InfoSenderReceiver.getCurrentTotal(currentTotal);
				InfoSenderReceiver.getProduct(aProduct);
				Receipt.addItem(aProduct);
				Transaction.addItem(aProduct);
			}
			
			else{
				InfoSenderReceiver.checkFraud(checkingfraud);
				
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
			

	
		
		InfoSenderReceiver.getTotalPrice(currentTotal);
		amountTendered = InfoSenderReceiver.getAmountTendererd();
		change = ChangeGenerator.generateChange(currentTotal, amountTendered);
		InfoSenderReceiver.getChange(change);
		}
	}
}}}}
	
