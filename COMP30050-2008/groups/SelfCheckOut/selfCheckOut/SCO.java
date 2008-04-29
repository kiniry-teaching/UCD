package selfCheckOut;

/** This class launches the SelfCheckOut program.
 * @author Peter Gibney
 * @version 31st March 2008.
 * to run from within bin java selfCheckOut.SCO "IP address"
 * The IP address of machine transmitting the barcodes and weights must
 * be passed on the command line
 * 
 */
public class SCO {

	private static SelfCheckOut sco = null;
	//The IP address of machine transmitting the barcodes and weights must
	//be passed on the command line as a string
	public static void main(String[] args) {
		sco = new SelfCheckOut(args[0]);
		sco.start();
	}

}
