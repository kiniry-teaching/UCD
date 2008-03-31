package selfCheckOut;
/**
 * This  class is used to hold a weight
 *  for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 * @version 30th March 2008.
 */

public class Weight {
	
	private int weight;
	private long timeStamp = 0;
	
	public Weight(int weight) {
		this.weight = weight;
		timeStamp = System.currentTimeMillis();
	}

	// ------------------------------------------------
	/**
	 * Converts this Weight object to a String.
	 * 
	 * @return the Weight as a String.
	 */
	// ---------------------------------------------------------
	public String toString() {
		return "" + weight ;
	}
	// ---------------------------------------------
	/**
	 * Gets the time stamp for when this object was created.
	 * 
	 * @return the time stamp when the BarCode object was created.
	 */
	// ---------------------------------------------
	public long getTimeStamp() {
		return timeStamp;
	}
	// ---------------------------------------------
	public int getWeight() {
		return weight;
	}
	// ---------------------------------------------
}
