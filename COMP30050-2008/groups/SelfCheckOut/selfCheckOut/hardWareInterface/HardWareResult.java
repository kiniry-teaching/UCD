package selfCheckOut.hardWareInterface;
/**
 * This  class is used to hold a Barcodes and weights
 *  for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 * @version 15th April 2008.
 */
import selfCheckOut.BarCode;
import selfCheckOut.Weight;

public class HardWareResult {

	private final BarCode[] barCodes;//array of barcodes
	private final int numBarCodes; //the number of codes in array
	private final Weight weightPre;
	private final Weight weightPost;
	private final long timeStamp; //when the object was created
	// ----------------------------------------------------
	/**
	 * Creates a HardWareResult object.
	 * @param barCodes the array of BarCodes
	 * @param WeightPre the Weight object for the scales where initial 
	 * shopping is placed before barcode scanning, pre scanning
	 * @param WeightPost the Weight object for the scales where shopping is placed 
	 * after barcode scanning, post scanning
	 * @throws IllegalArgumentException if all params are null.	
	 * @throws IllegalArgumentException if length of barCodes array is = 0.
	 */
	// -----------------------------------------------------------
	public HardWareResult(BarCode[] barCodes,
							Weight weightPre,
							Weight weightPost) {
		if ((weightPre == null) && (weightPost == null) && (barCodes == null)) 
			throw new IllegalArgumentException(
				"HardWareResult(), all params null");
		if ((barCodes != null) && (barCodes.length == 0))   
				throw new IllegalArgumentException(
					"HardWareResult(), all barcodes length = 0");
		this.weightPre = weightPre;
		this.weightPost = weightPost;
		this.barCodes = barCodes; 
		if (barCodes == null) {
			numBarCodes = 0;
		} else {
			numBarCodes = this.barCodes.length;
		}
		timeStamp = System.currentTimeMillis();
	}
	// ---------------------------------------------
	/**
	 * Gets the time stamp for when this object was created.
	 * 
	 * @return the time stamp when the HardWareResult object was created.
	 */
	// ---------------------------------------------
	public long getTimeStamp() {
		return timeStamp;
	}
	// ---------------------------------------------
	/**
	 * Gets the number of BarCodes in the object.
	 * 
	 * @return the quantity of BarCodes stored in the object.
	 */
	// ---------------------------------------------
	public long getNumBarCodes() {
		return numBarCodes;
	}
	// ---------------------------------------------
	/**
	 * Gets the array of Barcodes.
	 * @return the array of Barcodes or null if none present.
	 */
	// ---------------------------------------------
	public BarCode[] getBarCodes() {
		return this.barCodes;
	}
	// ---------------------------------------------
	/**
	 * Gets the Weight objects or null if none.
	 * @param item which one to get, zero based, 
	 * 0 for WeightPre, 1 for WeightPost.
	 * @return the Weight object specified by index.
	 * @throws IllegalArgumentException if index not in [0,1]
	 */
	// ---------------------------------------------
	public Weight getWeight(int index) {
		if ((index >1) && index <0)
			throw new IllegalArgumentException(
				"HardWareResult().getWeight() index out of range");
		Weight tempWeight = null;
		if (index == 1) {
			tempWeight = this.weightPre;
		} else {
			tempWeight = this.weightPost;
		}
		return tempWeight;
	}
	// ------------------------------------------------
	/**
	 * Converts this HardWareResult object to a String.
	 * 
	 * @return this HardWareResult object as a String.
	 */
	// ---------------------------------------------------------
	public String toString() {
		String tempString = "WeightPre: ";
		if (this.weightPre != null) {
			tempString = tempString + this.weightPre.toString();
		} else {
			tempString = tempString + "NULL";
		}
		tempString = tempString + ", BarCode(s): ";
		if (barCodes != null) {
			for (int i = 0; i < numBarCodes; i++) {
				tempString = tempString + barCodes[i].toString() + " ";
			}
		} else {
			tempString = tempString + "NULL";
		}
		tempString = tempString + ", WeightPost: ";
		if (this.weightPost != null) {
			tempString = tempString + this.weightPost.toString();
		} else {
			tempString = tempString + "NULL";
		}
		return tempString;
	}
	// ---------------------------------------------
	/**
	 * Calculates the hash code for this Object.
	 * @return the hashcode as an int.
	 */
	// ---------------------------------------------
	public int hashCode() {
		int result = 17;
		if (this.weightPre != null) {
			result = 37*result + this.weightPre.hashCode();
		} else {
			result = 37*result;
		}
		if (this.weightPost != null) {
			result = 37*result + this.weightPost.hashCode();
		} else {
			result = 37*result;
		}
		if (barCodes != null) {
			for (int i = 0; i < this.numBarCodes; i++) {
				result = 37*result + barCodes[i].hashCode();
			}
		} else {
			result = 37*result;
		}
		return result;
	}
	// ---------------------------------------------
	/**
	 * Checks that the two HardWareResults are equal in all internal values.
	 * @param o the object to compare to.
	 * @return true if they are equal 
	 */
	public boolean equals(Object o) {
		boolean result = (o == this) && (o instanceof HardWareResult);
		//note instanceof has inbuilt null test
		HardWareResult hwr = (HardWareResult)o;
		result = result && (hwr.timeStamp == this.timeStamp);
		result = result && ((hwr.weightPre == null && this.weightPre == null) ||
							(hwr.weightPre!=null && this.weightPre!=null));
		if (result) {
			//get in here we know both are not null
			result = this.weightPre.equals(hwr.weightPre);
		}
		result = result && ((hwr.weightPost==null && this.weightPost==null) ||
					(hwr.weightPost!=null && this.weightPost!=null));
		if (result) {
			//get in here we know both are not null
			result = this.weightPost.equals(hwr.weightPost);
		}

		result = result && ((hwr.barCodes == null && this.barCodes == null) ||
				(hwr.barCodes != null && this.barCodes != null));

		if (result) {
			//get in here we know both are not null
			result = hwr.numBarCodes == this.numBarCodes;
			if (result) {
				//get in here we know both have the same number of codes
				for (int i = 0; i < this.numBarCodes; i++) {
					result = 
						result && this.barCodes[i].equals(hwr.barCodes[i]);
					if (!result)
						break;
				}
			}
		}
		return result;
	}
	// ---------------------------------------------
}//end class