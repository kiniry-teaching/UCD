package selfCheckOut.testCode;
import selfCheckOut.hardWareInterface.HardWareResult;
import selfCheckOut.netWork.PumpReciever;

/**
 * This class is used to test the PumpReciever class, the ip address is 
 * required on the command line.
 * <p>
 * @author Peter Gibney
 */

public class PumpRecieverTest02 {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		PumpReciever pr = new PumpReciever(args[0], 3333);
		pr.start();
		pr.gather(true);
		
		for (int i = 0; i < 5500; i++) {
			HardWareResult hwr = pr.getHardWareResult();
			
			if (hwr != null) {
				System.out.println("Server: " + hwr + ", i = " + i);//fromServer);
			}
			try {
				Thread.sleep( 100 );
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		
	}

}
