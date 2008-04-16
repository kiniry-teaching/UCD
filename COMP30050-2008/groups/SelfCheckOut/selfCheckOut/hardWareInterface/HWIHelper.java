package selfCheckOut.hardWareInterface;
/**
	 * This uninstantiable class is used to provide helper methods for the 
	 * HardWareInterface system.
	 * <p>
	 * This class can not be instantiated.
	 * 
	 * @author Peter Gibney
	 * @version 19th March 2008.
	 */

public class HWIHelper {

	/**
	 * This constructor is private.
	 * <p>
	 * Don't let anyone instantiate this class.
	 */
	private HWIHelper() { }
	
	
	//************************************************
	/**
	 * Converts int to space padded string.
	 * 
	 * @param  inPut the int to be converted to padded string
	 * @param len the length of padded str
	 * @return the padded string
	 * @author Peter Gibney
	 * @version 10th March 2008
	 */
	public static String padIntToString(int inPut, int len) {
		assert len > 0;
		String s = "" + inPut;
		int addLen = len - s.length();
		if (addLen < 1)
			return s;
		for (int i = 0 ; i < addLen ;++ i)
			s = " " + s;
		return s;
	}
	//**********************************************************
}
