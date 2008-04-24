//package selfCheckOut;
import java.io.Serializable;
import java.util.Scanner;


/**
 * This  class is used to hold a weight
 *  for the SelfChekcOut project.
 * <p>
 * @author Peter Gibney
 * @version 15th April 2008.
 */

public class Weight implements Serializable{
	
	private final int weight; //weight in grams
	private final long timeStamp; //when the object was created
	private static final long serialVersionUID = 2874454;
	
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
	// ------------------------------------------------------	
	/**
	 * Creates a Weight object from an int, and a timestamp long.
	 * @param weight the weight in grams.
	 * @param timeStamp the timestamp
	 * @throws IllegalArgumentException if weight is <0.
	 * @throws IllegalArgumentException if timestamp is <0.
	 */
	// ------------------------------------------------------
	public Weight(int weight, long timeStamp) {
		if (weight < 0)
			throw new IllegalArgumentException("Weight is negative = " 
					+ weight);
		if (timeStamp < 0)
			throw new IllegalArgumentException("TimeStamp is negative = " 
					+ timeStamp);
		this.weight = weight;
		this.timeStamp = timeStamp;
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
		boolean result = true; //assume same
		if (weight == null) {
			result = false;
		} else {
			if (this != weight) {
				result = (this.weight == weight.weight);
			}
		}
		return result;
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
		boolean result = true; //assumes equals
		if (o != this) {
			if (o instanceof Weight) { //includes a null test
				Weight w = (Weight)o;
				result = result && (w.weight == this.weight);
				result = result && (w.timeStamp == this.timeStamp);
			} else {
				result = false; //null or not Weight object
			}
		}	
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
	/**
	 * Exports this object as a formatted string so that it can be
	 * reconstructed usinig a corresponging importWeight(),
	 * These are intended to permit the persistance & transmission as strings.
	 * @return formatted string representing the object.
	 */
	public String exportWeight() {
		return "WeightStart: Weight: " + weight +
			" TimeStamp: " + timeStamp + 
			" serialVersionUID: " + serialVersionUID +
			" WeightStop:"; 
	}
	// ---------------------------------------------
	/**
	 * imports a formatted string reperesntation through a Scanner of a 
	 * Weight object and returns an object with those paramaters.
	 * @param inScan the Scanner object containing the the formatted 
	 * string representing the Weight object
	 * @return a Weight object made from the formatted string, null if one 
	 * can not be made from it which indicates an error.
	 */
	public static Weight importWeight(Scanner inScan) {
		int weightVal; //the value of weight in grams;
		long weightTimeStamp; //the timestamp
		long verSerial;
		Weight retWgt = null;
		if (inScan.hasNext("WeightStart:")) {
			inScan.next();//eat it, get rid of "WeightStart:"
			if (inScan.hasNext("Weight:")) {
				inScan.next();//get rid of it
				if (inScan.hasNextInt()) {
					weightVal = inScan.nextInt();
					if ((weightVal >=0) && (inScan.hasNext("TimeStamp:"))) {
						inScan.next();//get rid
						if (inScan.hasNextLong()) {
							weightTimeStamp = inScan.nextLong();
							if ((weightTimeStamp >= 0) &&
									(inScan.hasNext("serialVersionUID:"))) {
								inScan.next();//get rid
								if (inScan.hasNextLong()) {
									verSerial = inScan.nextLong();
									if ((verSerial == serialVersionUID)
											&& (inScan.hasNext("WeightStop:"))) {
										inScan.next();//get rid
										retWgt = 
												new Weight(weightVal, weightTimeStamp);
									}
								}
							}
						}
					}
				}
			}
		}
		return retWgt;
	}
	// --------------------------------------------------------------
	
	
} //end class Weight
