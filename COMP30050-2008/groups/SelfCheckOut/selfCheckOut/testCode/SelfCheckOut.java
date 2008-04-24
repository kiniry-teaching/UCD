/**
 * This  class is used as the main loop 
 *  for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 * @version 14th April 2008.
 */


//package selfCheckOut;

//import selfCheckOut.hardWareInterface.HWIconduit;
//import selfCheckOut.hardWareInterface.HardWareResult;

public class SelfCheckOut extends Thread {

	private HWIconduit hwc = null;
	
	SelfCheckOut(String ipAddress) {
		System.out.println("This is the test for the SelfCheckout project");
		hwc = new HWIconduit(ipAddress, 3333);
		hwc.start();
		hwc.gather(true);
		//Process();
	}
	
	public void run() {
		int counter = 0;
		while (true) {
			counter++;
			//if (counter == 90)
				//hwc.gather(false);
			HardWareResult temp = null;
			temp =  hwc.getHardWareResult();
			if (temp != null) {
				System.out.println("SCO: " + temp);
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
