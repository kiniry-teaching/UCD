package selfCheckOut;

/** This class launches the SelfCheckOut program.
 * @author Peter Gibney
 * @version 31st March 2008.

 */
public class SCO {

	private static SelfCheckOut sco = null;
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		sco = new SelfCheckOut();
		sco.start();
	}

}
