package selfCheckOut.testCode;
import selfCheckOut.netWork.PumpReciever;
import selfCheckOut.hardWareInterface.HardWareResult;

/**
 * This class is used to test the PumpReciever class, the ip address is 
 * required on the command line.
 * <p>
 * @author Peter Gibney
 */

public class PumpRecieverTest01 {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		PumpReciever pr = new PumpReciever(args[0], 4444);
		pr.start();
		
		for (int i = 0; i < 1500; i++) {
			HardWareResult hwr = pr.getHardWareResult();
			
			if (hwr != null) {
				System.out.println("Server: " + hwr);//fromServer);
			}
			try {
				Thread.sleep( 100 );
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		
	}

}
