//package selfCheckOut.hardWareInterface;
/**
 * This  class is used to hold a Barcodes and weights
 *  for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 * @version 15th April 2008.
 */
import java.util.Scanner;

//import selfCheckOut.BarCode;
//import selfCheckOut.Weight;

public class HardWareResult {

	private final BarCode[] barCodes;//array of barcodes
	private final Weight weightPre;
	private final Weight weightPost;
	private final long timeStamp; //when the object was created
	private static final long serialVersionUID = 2871569;
	// ----------------------------------------------------
	/**
	 * Creates a HardWareResult object.
	 * @param barCodes the array of BarCodes
	 * @param WeightPre the Weight object for the scales where initial 
	 * shopping is placed before barcode scanning, pre scanning
	 * @param WeightPost the Weight object for the scales where shopping is placed 
	 * after barcode scanning, post scanning
	 * @throws IllegalArgumentException if all params are null.	
	 * @throws IllegalArgumentException if length of barCodes array is = 0,
	 * and it is not null.
	 * @throws IllegalArgumentException if there is a null entry in barCodes.
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
					"HardWareResult(), barcodes[].length = 0, but not null");
		this.weightPre = weightPre;
		this.weightPost = weightPost;
		if (barCodes == null) {
			this.barCodes = null;
		} else {
			this.barCodes = new BarCode[barCodes.length];
			for (int i = 0; i < this.barCodes.length; i++) {
				if (barCodes[i] == null) {
					throw new IllegalArgumentException(
					"HardWareResult(), null entry in barcodes at pos " + i);
				} else {
					this.barCodes[i] = barCodes[i];
				}
			}
		}
		timeStamp = System.currentTimeMillis();
	}	
	// ---------------------------------------------
	/**
	 * Creates a HardWareResult object.
	 * @param barCodes the array of BarCodes
	 * @param WeightPre the Weight object for the scales where initial 
	 * shopping is placed before barcode scanning, pre scanning
	 * @param WeightPost the Weight object for the scales where shopping is placed 
	 * after barcode scanning, post scanning
	 * @param timeStamp the timestamp
	 * @throws IllegalArgumentException if all first three params are null.	
	 * @throws IllegalArgumentException if length of barCodes array is = 0,
	 * and it is not null.
	 * @throws IllegalArgumentException if there is a null entry in barCodes.
	 * @throws IllegalArgumentException if timestamp is <0.
	 */
	// -----------------------------------------------------------
	public HardWareResult(BarCode[] barCodes,
							Weight weightPre,
							Weight weightPost,
							long timeStamp) {
		if ((weightPre == null) && (weightPost == null) && (barCodes == null)) 
			throw new IllegalArgumentException(
				"HardWareResult(), all params null");
		if ((barCodes != null) && (barCodes.length == 0))   
				throw new IllegalArgumentException(
					"HardWareResult(), barcodes[].length = 0, but not null");
		if (timeStamp < 0)
			throw new IllegalArgumentException("TimeStamp is negative = " 
					+ timeStamp);
		this.weightPre = weightPre;
		this.weightPost = weightPost;
		if (barCodes == null) {
			this.barCodes = null;
		} else {
			this.barCodes = new BarCode[barCodes.length];
			for (int i = 0; i < this.barCodes.length; i++) {
				if (barCodes[i] == null) {
					throw new IllegalArgumentException(
					"HardWareResult(), null entry in barcodes at pos " + i);
				} else {
					this.barCodes[i] = barCodes[i];
				}
			}
		}
		this.timeStamp = timeStamp;
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
	public int getNumBarCodes() {
		int tempNum = 0;
		if (this.barCodes != null) {
			tempNum = this.barCodes.length;
		}
		return tempNum;
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
		if (index == 0) {
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
			for (int i = 0; i < this.barCodes.length; i++) {
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
			for (int i = 0; i < this.barCodes.length; i++) {
				result = 37*result + barCodes[i].hashCode();
			}
		} else {
			result = 37*result;
		}
		return result;
	}
	//----------------------------------------------
	/**
	 * Checks that the two arguments have the same state of nulness.
	 * @param item1 the first of the two objects to be compared.
	 * @param item2 the second of the two objects to be compared.
	 * @return true if they have equal nullness 
	 */
	//----------------------------------------------
	private boolean sameNullNess(Object item1, Object item2) {
		return (((item1 == null) && (item2 == null)) 
				||
				((item1 !=null) && (item2 !=null)));
	}
	// ---------------------------------------------
	/**
	 * Checks that the two HardWareResults are equal in all internal values.
	 * @param o the object to compare to.
	 * @return true if they are equal 
	 */
	// ---------------------------------------------
	public boolean equals(Object o) {
		boolean result = true; //assumes equals
		if (o != this) {
			if (o instanceof HardWareResult) { //includes a null test
				HardWareResult hwr = (HardWareResult)o;
				result = this.timeStamp == hwr.timeStamp;
				result = result && sameNullNess(hwr.weightPre, this.weightPre);
				if (result && (hwr.weightPre !=null)) {
					//get in here we know both are not null
					result = this.weightPre.equals(hwr.weightPre);
				}
				result= result && sameNullNess(hwr.weightPost, this.weightPost);
				if (result && (hwr.weightPost !=null)) {
					//get in here we know both are not null
					result = this.weightPost.equals(hwr.weightPost);
				}
				result = result && sameNullNess(hwr.barCodes, this.barCodes);
				if (result && (this.barCodes != null)) {
					//get in here we know both are not null
					for (int i = 0; i < this.barCodes.length; i++) {
						result = 
							result && this.barCodes[i].equals(hwr.barCodes[i]);
						if (!result)
							break;
					}
				}
			} else {
				result = false; //null or not HardWareResult object
			}
		}	
		return result;
	}
	// ---------------------------------------------
	/**
	 * Checks that the two HardWareResults are equal in BarCode & weight 
	 * values, this does not compare probabilities and time stamps.
	 * @param hwr the HardWareResults you want to compare to.
	 * @return true if they have the same values. 
	 */
	// ---------------------------------------------
	public boolean sameValues(HardWareResult hwr) {
		boolean result = true; //assumes equals
		if (hwr == null) {
			result = false;
		} else {
			if (this != hwr) {
				result = result && sameNullNess(hwr.weightPre, this.weightPre);
				if (result && (hwr.weightPre !=null)) {
					//get in here we know both are not null
					result = this.weightPre.sameWeightValue(hwr.weightPre);
				}
				result= result && sameNullNess(hwr.weightPost, this.weightPost);
				if (result && (hwr.weightPost !=null)) {
					//get in here we know both are not null
					result = this.weightPost.sameWeightValue(hwr.weightPost);
				}
				result = result && sameNullNess(hwr.barCodes, this.barCodes);
				if (result && (this.barCodes != null)) {
					//get in here we know both are not null
					for (int i = 0; i < this.barCodes.length; i++) {
						result = 
							result && 
							this.barCodes[i].sameBarCodeValue(hwr.barCodes[i]);
						if (!result)
							break;
					}
				}
			}
		}
		return result;
	}
	// ---------------------------------------------
	/**
	 * Exports this object as a formatted string so that it can be
	 * reconstructed usinig the corresponging importHardWareResult(),
	 * These are intended to permit the persistance & transmission as strings.
	 * @return formatted string representing the object.
	 */
	public String exportHardWareResult() {
		String resStr = "HardWareResultStart: TimeStamp: " + timeStamp + 
						" serialVersionUID: " + serialVersionUID;

		if (weightPre == null) {
			resStr = resStr + " weightPreIsNull:";
		} else {
			resStr = resStr + " weightPreIsNotNull: " + 
				weightPre.exportWeight();
		}

		if (weightPost == null) {
			resStr = resStr + " weightPostIsNull:";
		} else {
			resStr = resStr + " weightPostIsNotNull: " + 
				weightPost.exportWeight();
		}
		int barCodesLen;
		if (barCodes != null) {
			barCodesLen = barCodes.length;
		} else {
			barCodesLen = 0;
		}
		if (barCodesLen == 0) {
			resStr = resStr + " barCodesLen: 0";
		} else {
			resStr = resStr + " barCodesLen: " + barCodesLen;
			for (int i = 0; i < barCodesLen; i++) {
				resStr = resStr + " BarCode_" + i + "_: ";
				resStr = resStr + barCodes[i].exportBarCode();
			}
		}	
		resStr = resStr + " HardWareResultStop:"; 
		return resStr;
	}
	// ---------------------------------------------
	public static HardWareResult importHardWareResult(Scanner inScan) {
		BarCode[] barCodes = null;//array of barcodes
		Weight weightPre = null;
		Weight weightPost = null;
		long timeStamp = 0; //when the object was created
		long verSerial;
		int numBarCodes = 0;
		boolean readError = true;
		HardWareResult hwr = null;
		if (inScan.hasNext("HardWareResultStart:")) {
			inScan.next();//eat it, get rid of "HardWareResultStart:"
			if (inScan.hasNext("TimeStamp:")) {
				inScan.next();//get rid of it "TimeStamp:"
				if (inScan.hasNextLong()) {
					timeStamp = inScan.nextLong();
					if ((timeStamp >= 1) && 
							(timeStamp <= 9999999999999l) &&
							inScan.hasNext("serialVersionUID:")) {
						inScan.next();//get rid of it , ("serialVersionUID:")
						if (inScan.hasNextLong()) {
							verSerial = inScan.nextLong();
							if (verSerial == serialVersionUID) {
								readError = false;
							}
						}
					}
				}
			}
		}
		if (!readError) {
			//so far reading is OK
			if (inScan.hasNext("weightPreIsNull:")) {
				//we have no value for weight pre
				inScan.next();//get rid of it "weightPreIsNull:"
			} else {
				if (inScan.hasNext("weightPreIsNotNull:")) {
					inScan.next();//get rid of it "weightPreIsNotNull:"
					weightPre = Weight.importWeight(inScan);
					if (weightPre == null) {
						//something wrong, have an error
						readError = true;
					}
				}else {
					//something wrong, have an error
					readError = true;
				}
			}
		}
		if (!readError) {
			//so far reading is OK
			if (inScan.hasNext("weightPostIsNull:")) {
				//we have no value for weight post
				inScan.next();//get rid of it "weightPostIsNull:"
			} else {
				if (inScan.hasNext("weightPostIsNotNull:")) {
					inScan.next();//get rid of it "weightPostIsNotNull:"
					weightPost = Weight.importWeight(inScan);
					if (weightPost == null) {
						//something wrong, have an error
						readError = true;
					}
				}else {
					//something wrong, have an error
					readError = true;
				}
			}
		}
		if (!readError) {
			//so far reading is OK
			if (inScan.hasNext("barCodesLen:")) {
				inScan.next();//get rid of it
				//look to see how many barcodes there are
				if (inScan.hasNextInt()) {
					numBarCodes = inScan.nextInt();
					if (numBarCodes < 0) {
						readError = true;
					}
				} else {
					readError = true;
				}
			} else {
				readError = true;
			}
		}
		if (!readError) {
			if (numBarCodes > 0) {
				barCodes = new BarCode[numBarCodes];//array of barcodes
				for (int i = 0; i < numBarCodes; i++) {
					String nextTrigger = "BarCode_" + i + "_:";
					if (inScan.hasNext(nextTrigger)) {
						inScan.next();//get rid of it
						barCodes[i] = BarCode.importBarCode(inScan);
						if (barCodes[i] == null) {
							//something wrong, have an error
							readError = true;
						}
					} else {
						readError = true;
					}
				}
			}
		}
		if (!readError && (inScan.hasNext("HardWareResultStop:"))) {
			inScan.next();//get rid of it
			//success
			hwr = new HardWareResult(barCodes,
									weightPre,
									weightPost,
									timeStamp);
		}
		return hwr;
	}
	// ---------------------------------------------
}//end class