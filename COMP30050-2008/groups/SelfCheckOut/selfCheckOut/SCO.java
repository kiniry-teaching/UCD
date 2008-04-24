package selfCheckOut;

/** This class launches the SelfCheckOut program.
 * @author Peter Gibney
 * @version 31st March 2008.
 * to run from withn bin java selfCheckOut.SCO
 */
public class SCO {

	private static SelfCheckOut sco = null;
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		sco = new SelfCheckOut(args[0]);
		sco.start();
	}

}
