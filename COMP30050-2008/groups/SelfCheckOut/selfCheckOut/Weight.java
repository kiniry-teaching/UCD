package selfCheckOut;
/**
 * This  class is used to hold a weight
 *  for the SelfChekcOut project.
 * <p>
 * @author Peter Gibney
 * @version 15th April 2008.
 */

public class Weight {
	
	private final int weight; //weight in grams
	private final long timeStamp; //when the object was created
	
	// ------------------------------------------------------	
	/**
	 * Creates a Weight object from an int.
	 * @param weight the weight in grams.
	 * @throws IllegalArgumentException if weight is <0.
	 */
	// ------------------------------------------------------
	public Weight(int weight) {
		if (weight < 0)
			throw new IllegalArgumentException("Weight is negative = " 
					+ weight);
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
	/**
	 * Gets the weight as an int.
	 * 
	 * @return the weight in grams.
	 */
	// ---------------------------------------------
	public int getWeightInt() {
		return weight;
	}
	// ---------------------------------------------
	/**
	 * Checks that the two Weights have the same weight value.
	 * @param weight the Weight you want to compare to
	 * @return true if they have the same weight value, this does not compare 
	 * the timestamps.
	 */
	// ---------------------------------------------
	public boolean sameWeightValue(Weight weight) {
		return (this.weight == weight.weight);
	}
	// ---------------------------------------------
	/**
	 * Calculates the hash code for this Weight.
	 * @return the hashcode as an int.
	 */
	// ---------------------------------------------
	public int hashCode() {
		int result = 17;
		result = 37*result + (int)(timeStamp ^ (timeStamp >>>32));
		result = 37*result + weight;
		return result;
	}
	// ---------------------------------------------
	/**
	 * Checks that the two Weights are equal in all internal values.
	 * @param o the object to compare to.
	 * @return true if they are equal 
	 */
	public boolean equals(Object o) {
		boolean result = (o == this) && (o instanceof Weight);
		Weight w = (Weight)o;
		result = result && (w.weight == this.weight);
		result = result && (w.timeStamp == this.timeStamp);
		return result;
	}
	// ---------------------------------------------
	/**
	 * Checks that this weight is in the tolerance of the other two.
	 * @param lower the lower tolerance weight
	 * @param lower the lower tolerance weight
	 * @return true if in tolerance.
	 */
	public boolean inTolerance(Weight lower, Weight upper) {
		return ((this.weight <= upper.weight) && (this.weight >= lower.weight)); 
	}
	// ---------------------------------------------
} //end class Weight
