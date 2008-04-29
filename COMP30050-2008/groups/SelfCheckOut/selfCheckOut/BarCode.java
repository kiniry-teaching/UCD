package selfCheckOut;

import java.util.Scanner;

	/**
	 * This  class is used to hold a Barcode for the SelfChekcOut project.
	 * <p>
	 * 
	 * @author Peter Gibney
	 * @version 15th April 2008.
	 */
public class BarCode {
	//
	private static final int BAR_CODE_LEN = 13;
	private final int[] barNums = new int[BAR_CODE_LEN];
	private final long timeStamp;
	private final double probability;
	private static final long serialVersionUID = 8421863;

	// ------------------------------------------------------	
	/**
	 * Creates a Barcode object from an array of ints.
	 * @param barNums the array of ints, 13 long
	 * @throws IllegalArgumentException if barNums is null.
	 * @throws IllegalArgumentException if barNums is not length 13.
	 * @throws IllegalArgumentException if an element of barNums is <0.
	 * @throws IllegalArgumentException if an element of barNums is >9.
	 * @throws IllegalArgumentException if the code is not a valid code.
	 */
	// ------------------------------------------------------
	public BarCode(int[] barNums) {
		if (barNums == null)
			throw new IllegalArgumentException("BarCode() barNums[] is null");
		if (barNums.length != BAR_CODE_LEN)
			throw new IllegalArgumentException("Barcode() barNums[] " +
					"is wrong length = " + barNums.length);
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			this.barNums[i] = barNums[i];
			if (barNums[i] < 0)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element greater than 10 = " + barNums[i]);
		}
		 if (!isValid())
			throw new IllegalArgumentException("BarCode() is not a valid code");
		timeStamp = System.currentTimeMillis();
		probability = 1d;
	}
	//------------------------------------------------------	
	/**
	 * Creates a Barcode object from an array of ints,
	 * and a double for probality measure .
	 * @param barNums the array of int, 13 long
	 * @param barProb the probability that this is the code
	 * @throws IllegalArgumentException if barNums is null.
	 * @throws IllegalArgumentException if barNums is not length 13.
	 * @throws IllegalArgumentException if an element of barNums is <0.
	 * @throws IllegalArgumentException if an element of barNums is >9.
	 * @throws IllegalArgumentException if the code is not a valid code.
	 * @throws IllegalArgumentException if barProb > 1.
	 * @throws IllegalArgumentException if barProb < 0.
	 * @throws IllegalArgumentException if barProb is NaN.
	 */
	// ------------------------------------------------------
	public BarCode(int[] barNums, double barProb) {
		if (barNums == null)
			throw new IllegalArgumentException("BarCode() barNums[] is null");
		if (barNums.length != BAR_CODE_LEN)
			throw new IllegalArgumentException("Barcode() barNums[] " +
					"is wrong length = " + barNums.length);
		if (barProb < 0d)
			throw new IllegalArgumentException("Barcode() barProb " +
					"is negative = " + barProb);
		if (barProb > 1d)
			throw new IllegalArgumentException("Barcode() barProb " +
					"is too big = " + barProb);
		if (Double.isNaN(barProb))
			throw new IllegalArgumentException("Barcode() barProb is NaN");
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			this.barNums[i] = barNums[i];
			if (barNums[i] < 0)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element greater than 10 = " + barNums[i]);
		}
		if (!isValid())
			throw new IllegalArgumentException("BarCode() is not a valid code");
		probability = barProb;
		timeStamp = System.currentTimeMillis();
	}
	// ------------------------------------------------------	
	/**
	 * Creates a Barcode object from an array of ints,
	 * and array of doubles for digit probabilities .
	 * @param barNums the array of int, 13 long
	 * @param barProbs the array of double, 13 long
	 * @throws IllegalArgumentException if barNums is null.
	 * @throws IllegalArgumentException if barNums is not length 13.
	 * @throws IllegalArgumentException if an element of barNums is <0.
	 * @throws IllegalArgumentException if an element of barNums is >9.
	 * @throws IllegalArgumentException if the code is not a valid code.
	 * @throws IllegalArgumentException if barProbs is null.
	 * @throws IllegalArgumentException if barProbs is not length 13.
	 * @throws IllegalArgumentException if an element of barProbs is < 0.
	 * @throws IllegalArgumentException if an element of barProbs is > 1.
	 * @throws IllegalArgumentException if barProb is NaN.
	 */
	// ------------------------------------------------------
	public BarCode(int[] barNums, double[] barProbs) {
		if (barNums == null)
			throw new IllegalArgumentException("BarCode() barNums[] is null");
		if (barNums.length != BAR_CODE_LEN)
			throw new IllegalArgumentException("Barcode() barNums[] " +
					"is wrong length = " + barNums.length);
		if (barProbs == null)
			throw new IllegalArgumentException("BarCode() barProbs[] is null");
		if (barProbs.length != BAR_CODE_LEN)
			throw new IllegalArgumentException("Barcode() barProbs[] " +
					"is wrong length = " + barNums.length);
		double tempProbability = 1d;
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			this.barNums[i] = barNums[i];
			if (barNums[i] < 0)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element greater than 10 = " + barNums[i]);
			if (barProbs[i] < 0d)
				throw new IllegalArgumentException("Barcode() barProbs[] " +
						"has negative elements = " + barProbs[i]);
			if (barProbs[i] > 1d)
				throw new IllegalArgumentException("Barcode() barProbs[] " +
						"has element too big = " + barProbs[i]);
			if (Double.isNaN(barProbs[i]))
				throw new IllegalArgumentException("Barcode() barProb is NaN");
			tempProbability = tempProbability * barProbs[i];
		}
		probability = tempProbability;
		if (!isValid())
			throw new IllegalArgumentException("BarCode() is not a valid code");
		timeStamp = System.currentTimeMillis();
	}
	// ------------------------------------------------------	
	/**
	 * Creates a Barcode object from an array of ints,
	 * and array of doubles for digit probabilities,
	 * and a long representing the time stamp.
	 * @param barNums the array of int, 13 long
	 * @param barProbs the array of double, 13 long
	 * @param timeStamp the time stamp for the barcode
	 * @throws IllegalArgumentException if barNums is null.
	 * @throws IllegalArgumentException if barNums is not length 13.
	 * @throws IllegalArgumentException if an element of barNums is <0.
	 * @throws IllegalArgumentException if an element of barNums is >9.
	 * @throws IllegalArgumentException if the code is not a valid code.
	 * @throws IllegalArgumentException if barProbs is null.
	 * @throws IllegalArgumentException if barProbs is not length 13.
	 * @throws IllegalArgumentException if an element of barProbs is < 0.
	 * @throws IllegalArgumentException if an element of barProbs is > 1.
	 * @throws IllegalArgumentException if barProb is NaN.
	 * @throws IllegalArgumentException if timestamp is <0.
	 */
	// ------------------------------------------------------
	public BarCode(int[] barNums, double[] barProbs, Long timeStamp) {
		if (barNums == null)
			throw new IllegalArgumentException("BarCode() barNums[] is null");
		if (barNums.length != BAR_CODE_LEN)
			throw new IllegalArgumentException("Barcode() barNums[] " +
					"is wrong length = " + barNums.length);
		if (barProbs == null)
			throw new IllegalArgumentException("BarCode() barProbs[] is null");
		if (barProbs.length != BAR_CODE_LEN)
			throw new IllegalArgumentException("Barcode() barProbs[] " +
					"is wrong length = " + barNums.length);
		if (timeStamp <0)
			throw new IllegalArgumentException("BarCode() timeStamp too small");
		double tempProbability = 1d;
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			this.barNums[i] = barNums[i];
			if (barNums[i] < 0)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element greater than 10 = " + barNums[i]);
			if (barProbs[i] < 0d)
				throw new IllegalArgumentException("Barcode() barProbs[] " +
						"has negative elements = " + barProbs[i]);
			if (barProbs[i] > 1d)
				throw new IllegalArgumentException("Barcode() barProbs[] " +
						"has element too big = " + barProbs[i]);
			if (Double.isNaN(barProbs[i]))
				throw new IllegalArgumentException("Barcode() barProb is NaN");
			tempProbability = tempProbability * barProbs[i];
		}
		probability = tempProbability;
		if (!isValid())
			throw new IllegalArgumentException("BarCode() is not a valid code");
		this.timeStamp = timeStamp;
	}
	// ------------------------------------------------------
	/**
	 * Creates a Barcode object from an array of ints,
	 * and a double for probality measure .
	 * @param barNums the array of int, 13 long
	 * @param barProb the probability that this is the code
	 * @throws IllegalArgumentException if barNums is null.
	 * @throws IllegalArgumentException if barNums is not length 13.
	 * @throws IllegalArgumentException if an element of barNums is <0.
	 * @throws IllegalArgumentException if an element of barNums is >9.
	 * @throws IllegalArgumentException if the code is not a valid code.
	 * @throws IllegalArgumentException if barProb > 1.
	 * @throws IllegalArgumentException if barProb < 0.
	 * @throws IllegalArgumentException if barProb is NaN.
	 * @throws IllegalArgumentException if timestamp is <0.
	 */
	// ------------------------------------------------------
	public BarCode(int[] barNums, double barProb, Long timeStamp) {
		if (barNums == null)
			throw new IllegalArgumentException("BarCode() barNums[] is null");
		if (barNums.length != BAR_CODE_LEN)
			throw new IllegalArgumentException("Barcode() barNums[] " +
					"is wrong length = " + barNums.length);
		if (barProb < 0d)
			throw new IllegalArgumentException("Barcode() barProb " +
					"is negative = " + barProb);
		if (barProb > 1d)
			throw new IllegalArgumentException("Barcode() barProb " +
					"is too big = " + barProb);
		if (Double.isNaN(barProb))
			throw new IllegalArgumentException("Barcode() barProb is NaN");
		if (timeStamp <0)
			throw new IllegalArgumentException("BarCode() timeStamp too small");
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			this.barNums[i] = barNums[i];
			if (barNums[i] < 0)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element greater than 10 = " + barNums[i]);
		}
		if (!isValid())
			throw new IllegalArgumentException("BarCode() is not a valid code");
		probability = barProb;
		this.timeStamp = timeStamp;
	}
	// ------------------------------------------------------
	/**
	 * Creates a Barcode object from a long.
	 * @param barNum the long to create the barcode from
	 * @throws IllegalArgumentException if barNum is <1.
	 * @throws IllegalArgumentException if barNum > 9999999999999.
	 * @throws IllegalArgumentException if the code is not a valid code.
	 */
	// ------------------------------------------------------
	public BarCode(long barNum) {
		if (barNum < 1l) //note the last character is lower case L
			throw new IllegalArgumentException("BarCode() barNum is < 1");
		if (barNum > 9999999999999l)//note the last character is lower case L
			throw new IllegalArgumentException("Barcode() barNum " +
					"is too large, max= " + 9999999999999l);
		String tempStr = barNum + "";
		//pad it with zeroes
		String zeroes = "0000000000000";
		tempStr = zeroes.substring(0,13-tempStr.length()) + tempStr;
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			barNums[i] = Integer.parseInt(tempStr.substring(i,i+1));
			if (barNums[i] < 0)
				throw new IllegalArgumentException("BarCode() barNum has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("BarCode() barNum has" +
						" element greater than 9 = " + barNums[i]);
		}
		if (!isValid())
			throw new IllegalArgumentException("BarCode() is not a valid code");
		timeStamp = System.currentTimeMillis();
		probability = 1d;
	}
	// ------------------------------------------------------	
	/**
	 * Creates a Barcode object from a long and a stated probability.
	 * @param barNum the long to create the barcode from
	 * @param barProb the probability that this is the code
	 * @throws IllegalArgumentException if barNum is <1.
	 * @throws IllegalArgumentException if barNum > 999999999999.
	 * @throws IllegalArgumentException if the code is not a valid code.
	 * @throws IllegalArgumentException if barProb > 1.
	 * @throws IllegalArgumentException if barProb < 0.
	 * @throws IllegalArgumentException if barProb is NaN.
	 */
	// ------------------------------------------------------
	public BarCode(long barNum, double barProb) {
		if (barNum < 1)
			throw new IllegalArgumentException("BarCode() barNum is < 1");
		if (barNum > 9999999999999l)
			throw new IllegalArgumentException("Barcode() barNum " +
					"is too large, max= " + 9999999999999l);
		if (barProb < 0d)
			throw new IllegalArgumentException("Barcode() barProb " +
					"is negative = " + barProb);
		if (barProb > 1d)
			throw new IllegalArgumentException("Barcode() barProb " +
					"is too big = " + barProb);
		if (Double.isNaN(barProb))
			throw new IllegalArgumentException("Barcode() barProb is NaN");
		String tempStr = barNum + "";
		//pad it with zeroes
		String zeroes = "0000000000000";
		tempStr = zeroes.substring(0,13-tempStr.length()) + tempStr;
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			barNums[i] = Integer.parseInt(tempStr.substring(i,i+1));
			if (barNums[i] < 0)
				throw new IllegalArgumentException("BarCode() barNum has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("BarCode() barNum has" +
						" element greater than 9 = " + barNums[i]);
		}
		 if (!isValid())
			throw new IllegalArgumentException("BarCode() is not a valid code");
		timeStamp = System.currentTimeMillis();
		probability = barProb;
	}
	// ------------------------------------------------------	
	/**
	 * Creates a Barcode object from a long, a stated probability as a 
	 * double and a timeStamp as a long.
	 * @param barNum the long to create the barcode from
	 * @param barProb the probability that this is the code
	 * @param barNum the long to create the timeStamp from
	 * @throws IllegalArgumentException if barNum is <1.
	 * @throws IllegalArgumentException if barNum > 999999999999.
	 * @throws IllegalArgumentException if the code is not a valid code.
	 * @throws IllegalArgumentException if barProb > 1.
	 * @throws IllegalArgumentException if barProb < 0.
	 * @throws IllegalArgumentException if barProb is NaN.
	 * @throws IllegalArgumentException if timestamp is <0.
	 */
	// ------------------------------------------------------
	public BarCode(long barNum, double barProb, long timeStamp) {
		if (barNum < 1)
			throw new IllegalArgumentException("BarCode() barNum is < 1");
		if (barNum > 9999999999999l)
			throw new IllegalArgumentException("Barcode() barNum " +
					"is too large, max= " + 9999999999999l);
		if (barProb < 0d)
			throw new IllegalArgumentException("Barcode() barProb " +
					"is negative = " + barProb);
		if (barProb > 1d)
			throw new IllegalArgumentException("Barcode() barProb " +
					"is too big = " + barProb);
		if (Double.isNaN(barProb))
			throw new IllegalArgumentException("Barcode() barProb is NaN");
		if (timeStamp <0)
			throw new IllegalArgumentException("BarCode() timeStamp too small");
		String tempStr = barNum + "";
		//pad it with zeroes
		String zeroes = "0000000000000";
		tempStr = zeroes.substring(0,13-tempStr.length()) + tempStr;
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			barNums[i] = Integer.parseInt(tempStr.substring(i,i+1));
			if (barNums[i] < 0)
				throw new IllegalArgumentException("BarCode() barNum has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("BarCode() barNum has" +
						" element greater than 9 = " + barNums[i]);
		}
		 if (!isValid())
			throw new IllegalArgumentException("BarCode() is not a valid code");
		this.timeStamp = timeStamp;
		probability = barProb;
	}
	// ------------------------------------------------------	
	/**
	 * Creates a Barcode object from a string.
	 * @param codeStr
	 * @throws IllegalArgumentException if String codeStr is null.
	 * @throws IllegalArgumentException if String codeStr is not length 13.
	 * @throws IllegalArgumentException if an element of codeStr is <0.
	 * @throws IllegalArgumentException if an element of codeStr is >9.
	 * @throws IllegalArgumentException if the code is not a valid code.
	 */
	// ------------------------------------------------------	
	public BarCode(String codeStr) {
		if (codeStr == null)
			throw new IllegalArgumentException("BarCode() code is null");
		if (codeStr.length() != BAR_CODE_LEN)
			throw new IllegalArgumentException("BarCode() codeStr " +
					"is wrong length = " + codeStr.length());
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			barNums[i] = Integer.parseInt(codeStr.substring(i,i+1));
			if (barNums[i] < 0)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element greater than 9 = " + barNums[i]);
		}
		if (!isValid())
			throw new IllegalArgumentException("BarCode() is not a valid code");
		timeStamp = System.currentTimeMillis();
		probability = 1d;
	}
	// ------------------------------------------------
	/**
	 * Converts this Barcode object to a String.
	 * 
	 * @return the barcode as a String.
	 */
	// ---------------------------------------------------------
	public String toString() {
		String str = "";
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			assert barNums[i] >= -1;
			assert barNums[i] <= 9;
			str = str + barNums[i];
		}
		return str;
	}
	// -------------------------------------------------------------
	/**
	 * Checks if the barcode is a valid.
	 * 
	 * @return true if the code is valid.
	 */
	// --------------------------------------------------
	private boolean isValid() {
		int checkSum = barNums[0] + barNums[2] + barNums[4] + 
						barNums[6] + barNums[8] + barNums[10] + 
						(3*(barNums[1] + barNums[3] + barNums[5] + 
						barNums[7] + barNums[9] + barNums[11]));
		int checkSumValue = 10 - (checkSum % 10);
		if (checkSumValue == 10)
			checkSumValue = 0;
		return (barNums[12] == checkSumValue);
	}
	// ----------------------------------------------------
	/**
	 * Gets the barcode as an array of numbers.
	 * 
	 * @return an array containing the numerical values of the 13 digits.
	 *
	 */
	// -----------------------------------------------------------
	public int[] getNumbers() {
		int[] retNums = new int[BAR_CODE_LEN]; 
		for (int i= 0; i<BAR_CODE_LEN;i++){
			retNums[i] = barNums[i];
		}
		return retNums;
	}
	// ----------------------------------------------------
	/**
	 * Gets the checkdigit for a potential barcode.
	 * 
	 * @param potentialCode the string representation of the 
	 * potential bar code, must be lenght 12
	 * @return an int equal to the check digit for the potential code.
	 * @throws IllegalArgumentException if String codeStr is not length 12.
	 * @throws IllegalArgumentException if String codeStr is null.
	 * @throws IllegalArgumentException if an element of codeStr is <0.
	 * @throws IllegalArgumentException if an element of codeStr is >9.
	 *
	 */
	// -----------------------------------------------------------
	public static int getPotentialCheckDigit(String potentialCode) {
		if (potentialCode == null)
			throw new IllegalArgumentException("BarCode() potentialCode is null");
		if (potentialCode.length() != BAR_CODE_LEN-1)
			throw new IllegalArgumentException("BarCode() potentialCode " +
					"is wrong length = " + potentialCode.length());
		int[] tempNums = new int[BAR_CODE_LEN-1];
		for (int i = 0; i < BAR_CODE_LEN-1; i++) {
			tempNums[i] = Integer.parseInt(potentialCode.substring(i,i+1));
			if (tempNums[i] < 0)
				throw new IllegalArgumentException("BarCode() potentialCode has" +
						" element less than 0 = " + tempNums[i]);
			if (tempNums[i] > 9)
				throw new IllegalArgumentException("BarCode() potentialCode has" +
						" element greater than 9 = " + tempNums[i]);
		}
		int checkSum = tempNums[0] + tempNums[2] + tempNums[4] + 
						tempNums[6] + tempNums[8] + tempNums[10] + 
						(3*(tempNums[1] + tempNums[3] + tempNums[5] + 
						tempNums[7] + tempNums[9] + tempNums[11]));
		checkSum = 10 - (checkSum % 10);
		if (checkSum == 10)
			checkSum = 0;
		return checkSum;
	}
	// ----------------------------------------------------
	/**
	 * Gets the checkdigit for a potential barcode.
	 * 
	 * @param potentialCode the intrepresentation of the 
	 * potential bar code, must be >=100000000000, <= 999999999999
	 * @return an int equal to the check digit for the potential code.
	 * @throws IllegalArgumentException if barNum is <100000000000.
	 * @throws IllegalArgumentException if barNum > 999999999999.
	 *
	 */
	// -----------------------------------------------------------
	public static int getPotentialCheckDigit(long potentialCode) {
		if (potentialCode < 100000000000l)//note last character is lower case L
			throw new IllegalArgumentException("BarCode() barNum is " +
					"< 100000000000");
		if (potentialCode > 999999999999l)//note last character is lower case L
			throw new IllegalArgumentException("Barcode() barNum " +
					"is too large, max= " + 999999999999l);
		return getPotentialCheckDigit("" + potentialCode);
	}
	// ----------------------------------------------------
	/**
	 * Gets the barcode as a long.
	 * 
	 * @return a BarCode as a long
	 *
	 */
	// -----------------------------------------------------------
	public long getBarCodeLong() {
		long tempLong = 0l;
		long multiplier = 1l;
		for (int i= BAR_CODE_LEN-1; i >= 0;i--){
			tempLong = tempLong + (barNums[i] * multiplier);
			multiplier = multiplier * 10l;//note last character is lower case L
		}
		return tempLong;
	}
	// ------------------------------------------------------	
	/**
	 * Gets a numerical value for the digit in a barcode, note zero based
	 * and counted from the left.
	 * @param index the digit you want
	 * @throws IllegalArgumentException if index is out of bounds,
	 * 			expecting 0 =< index <=12.
	 * @return the number at the index position.
	 */
	// ---------------------------------------------
	public int getNumber(int index) {
		if ((index >= 12) || (index <= 0)) 
			throw new IllegalArgumentException("BarCode.getNumber() passed " +
					"illegal argument index = " + index + 
					", expecting: 0 <= index <= 12");
		return barNums[index];
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
	 * Gets the probability of the barcode accuracy.
	 * 
	 * @return the probability of the barcode accuracy.
	 */
	// ---------------------------------------------
	public double getProbability() {
		return probability;
	}
	// ---------------------------------------------
	/**
	 * Checks that the two barcodes have the same barcode value.
	 * @param bc the BarCode you want to compare to
	 * @return true if they have the same value, this does not compare 
	 * the probability value or time stamps.
	 */
	// ---------------------------------------------
	public boolean sameBarCodeValue(BarCode bc) {
		boolean result = true; //assume same
		if (bc == null) {
			result = false;
		} else {
			if (this != bc) {
				for (int i= 0; i < BAR_CODE_LEN; i++) {
					result = result && (barNums[i] == bc.barNums[i]);
					if (!result) 
						break;
				}
			}
		}
		return result;
	}
	// ---------------------------------------------
	/**
	 * Calculates the hash code for this BarCode.
	 * @return the hashcode as an int.
	 */
	// ---------------------------------------------
	public int hashCode() {
		int result = 17;
		long probCode = Double.doubleToLongBits(probability);
		result = 37*result + (int)(timeStamp ^ (timeStamp >>>32));
		result = 37*result + (int)(probCode ^ (probCode >>>32));
		for (int i= 0; i < BAR_CODE_LEN; i++) {
			result = 37*result + barNums[i];
		}
		return result;
	}
	// ---------------------------------------------
	/**
	 * Checks that the two barcodes are equal in all internal values.
	 * @param o the object to compare to.
	 * @return true if they are equal 
	 */
	public boolean equals(Object o) {
		//System.out.println("o == this = " + (o == this));
		//System.out.println("(o instanceof BarCode) = " + (o instanceof BarCode));
		//System.out.println("o == null = " + (o == null));
		boolean result = true; //assumes equals
		if (o != this) {
			if (o instanceof BarCode) { //includes a null test
				BarCode bc = (BarCode)o;
				result = bc.timeStamp == this.timeStamp;
				//System.out.println(bc.timeStamp + " A " + bc.timeStamp + (bc.timeStamp == this.timeStamp));
				result = result && (bc.probability == this.probability);
				//System.out.println(bc.probability + " B " + bc.probability + (bc.probability == this.probability));
				for (int i= 0; i < BAR_CODE_LEN; i++) {
					result = result && (this.barNums[i] == bc.barNums[i]);
					//System.out.println(bc.barNums[i] + " C " + bc.barNums[i] + (bc.barNums[i] == this.barNums[i]));
					if (!result) 
						break;
				}
			} else {
				result = false; //null or not BarCode object
			}
		}	
		return result;
	}
	// ---------------------------------------------
	/**
	 * Exports this object as a formatted string so that it can be
	 * reconstructed usinig a corresponging importBarCode(),
	 * These are intended to permit the persistance & transmission as strings.
	 * @return formatted string representing the object.
	 */
	public String exportBarCode() {
		return "BarCodeStart: BarCode: " + this.toString() +
			" TimeStamp: " + timeStamp + 
			" Probability: " + probability +
			" serialVersionUID: " + serialVersionUID +
			" BarCodeStop:"; 
	}
	// ---------------------------------------------
	/**
	 * imports a formatted string reperesntation through a Scanner of a 
	 * BarCode object and returns an object with those paramaters.
	 * @param inScan the Scanner object containing the the formatted 
	 * string representing the BarCode object
	 * @return a BarCode object made from the formatted string, null if one 
	 * can not be made from it which indicates an error.
	 */

	public static BarCode importBarCode(Scanner inScan) {
		long barNum;
		double barProb;
		long barTimeStamp; //the timestamp
		long verSerial;
		BarCode retBarCode = null;
		if (inScan.hasNext("BarCodeStart:")) {
			inScan.next();//eat it, get rid of "BarCodeStart:"
			if (inScan.hasNext("BarCode:")) {
				inScan.next();//get rid of it
				if (inScan.hasNextLong()) {
					barNum = inScan.nextLong();
					if ((barNum >= 1) && 
							(barNum <= 9999999999999l) &&
							inScan.hasNext("TimeStamp:")) {
						inScan.next();//get rid of it , ("TimeStamp:")
						if (inScan.hasNextLong()) {
							barTimeStamp = inScan.nextLong();
							if ((barTimeStamp >= 0) &&
									(inScan.hasNext("Probability:"))) {
								inScan.next();//get rid "Probability:"
								if (inScan.hasNextDouble()) {
									barProb = inScan.nextDouble();
									if ((barProb >= 0d) && (barProb <= 1d) && 
										(inScan.hasNext("serialVersionUID:"))){
										inScan.next();
										//get rid "serialVersionUID:"
										if (inScan.hasNextLong()) {
											verSerial = inScan.nextLong();
											if ((verSerial == serialVersionUID)
													&& (inScan.hasNext("BarCodeStop:"))) {
												inScan.next();//get rid
												retBarCode =
													new BarCode(barNum, barProb, barTimeStamp);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		return retBarCode;
	}
	// --------------------------------------------------------------
} //end class BarCode