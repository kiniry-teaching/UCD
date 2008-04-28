
/**
 * This  class is used as the main loop 
 *  for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 * @version 14th April 2008.
 */


//package selfCheckOut;
//
//import selfCheckOut.hardWareInterface.HWIconduit;
//import selfCheckOut.userInterface.Ui;
//import selfCheckOut.hardWareInterface.HardWareResult;

public class SelfCheckOut extends Thread {

	private HWIconduit hwc = null;
	private  Ui testUi = null;
	
	SelfCheckOut(String AddressIP) {
		System.out.println("This is the test for the SelfCheckout project");
		
		testUi = new Ui(this);
		
		hwc = new HWIconduit(AddressIP, 3333);
		hwc.start();
		
		//Process();
	}
	
	public void startShopping() {
		System.out.println("startShopping() message recieved");
		hwc.gather(true);
	}
	
	public void stopShopping() {
		System.out.println("stopShopping() message recieved");
		hwc.gather(false);
	}
	
	
	
	public void hi() {
		
		System.out.println("HI from UI");
	}
	
	
	public void run() {
		int counter = 0;
		while (true) {
			counter++;
//			String ss = "peter " + counter;
//			testUi.write(ss);
			
			//if (counter == 90)
				//hwc.gather(false);
			HardWareResult temp = null;
			temp =  hwc.getHardWareResult();
			if (temp != null) {
				BarCode[] barCodes = temp.getBarCodes();
				System.out.println("\n");
				if (barCodes != null) { 
					for (int i = 0; i < barCodes.length; i++) {
						
						System.out.println("Query........");
						//create ItemQuery
						//System.out.println(barCodes[i].getBarCodeLong());
					//BarCode bc = new BarCode(3057640136993l);
						
						ItemQuery currItem = new ItemQuery(barCodes[i]);
						
						//System.out.println(currItem.toString());
						
						if(currItem.name == null)//if product for that 
						{
							System.out.println("Not A Valid Item");
						}
						else
						{
							System.out.println("Passing Item.....");
							testUi.displayItems(currItem);
						}
						
						
						
						
						
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
				} else {
					System.out.println("Barcode = NULL");
				}
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
				System.out.println("**************************************");
			}
			if (counter == 100) {
				System.out.print(".");
				hwc.gather(true);
				counter = 0;
			}

			try {
				sleep(50);
			} catch (InterruptedException e) {
				System.out.println("selfCheckOut() exception = " + e.toString());
				e.printStackTrace();
			}
		}
		
	}
}
