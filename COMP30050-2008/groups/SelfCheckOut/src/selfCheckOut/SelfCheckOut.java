/**
 * This class is used as the main loop 
 *  for the SelfChekcOut project, this is the slimmed down version without all
 *  Deidre's validation, voice announcer etc for the purpose of the demo for 
 *  Ross as we did not have the calipers to accuratly "set" the weights on
 *  the variable resistors attached to the Phidget.
 * <p>
 * 
 * @author Peter Gibney
 * @version 28th April 2008.
 */


package selfCheckOut;

import selfCheckOut.hardWareInterface.HWIconduit;
import selfCheckOut.hardWareInterface.HWIconst;
import selfCheckOut.userInterface.Ui;
import selfCheckOut.hardWareInterface.HardWareResult;
import selfCheckOut.dataBase.ItemQuery;

public class SelfCheckOut extends Thread {
	private HWIconduit hwc = null;
	private  Ui testUi = null;
	
	SelfCheckOut(String AddressIP) {
		System.out.println("This is the test for the SelfCheckout project");
		//set up the user interface
		testUi = new Ui(this);
		//start the communication to the barcode and weights virtual machine
		hwc = new HWIconduit(AddressIP, 3333);
		
	}
	
	// ---------------------------------------------
	/**
	 * Recieves a message from user interface to start receipt of 
	 * BarCodes and weigths, sent when a customer presses the 
	 * Start shopping button on the UI.
	 */
	public void startShopping() {
		System.out.println("startShopping() message recieved");
		hwc.gather(true);
	}
	// ---------------------------------------------
	/**
	 * Recieves a message from user interface to stop receipt of 
	 * BarCodes and weigths, sent when a customer presses the 
	 * Finish & pay button on the UI.
	 */
	public void stopShopping() {
		System.out.println("stopShopping() message recieved");
		hwc.gather(false);
	}
	
	public void run() {
		hwc.start();
		while (true) {
			//get the weights and barcodes
			HardWareResult temp = hwc.getHardWareResult();
			if (temp != null) {
				BarCode[] barCodes = temp.getBarCodes();
				System.out.println("\n");
				if (barCodes != null) { 
					//have an array of barcodes
					for (int i = 0; i < barCodes.length; i++) {
						
						System.out.println("Query........");
						//create ItemQuery
						//System.out.println(barCodes[i].getBarCodeLong());
						//BarCode bc = new BarCode(3057640136993l);
						ItemQuery currItem = new ItemQuery(barCodes[i]);
						//System.out.println(currItem.toString());
						if(currItem.name == null) {//if product for that 
							System.out.println("Not A Valid Item");
						} else {
							System.out.println("Passing Item.....");
							testUi.displayItems(currItem);
						}
						if (HWIconst.DE_BUG) {
							System.out.println("Barcode number " 
											+ i + " is " + 
											barCodes[i].toString() +
											", asLong " +
											barCodes[i].getBarCodeLong() +
											", time stamp= " +
											barCodes[i].getTimeStamp() + 
											", probability= " +
											barCodes[i].getProbability());
						}
					}
				} else {
					System.out.println("Barcode = NULL");
				}
				if (HWIconst.DE_BUG) {
					System.out.println("\n");
					for (int i = 1; i <= 2; i++) {
						Weight wgt = null;
						wgt = temp.getWeight(i);
						if (wgt != null) {
							System.out.println("Weight number " 
									+ i + " is " + 
									temp.getWeight(i).toString() +
									", time stamp= " +
									temp.getWeight(i).getTimeStamp());
						} else {
							System.out.println("Weight " + i + " = NULL");
						}
					}
				}
				System.out.println("**************************************");
			}
			try {
				sleep(150);
			} catch (InterruptedException e) {
				System.out.println("selfCheckOut() exception = " + e.toString());
				e.printStackTrace();
			}
		}
	}
}
