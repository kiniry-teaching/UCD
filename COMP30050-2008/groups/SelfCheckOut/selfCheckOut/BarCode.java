package selfCheckOut;

	/**
	 * This  class is used to hold a Barcode for the SelfChekcOut project.
	 * <p>
	 * 
	 * @author Peter Gibney
	 * @version 30th March 2008.
	 */
public class BarCode {

	private static final int BAR_CODE_LEN = 13;
	
	private int[] barNums = new int[BAR_CODE_LEN];
	private boolean hasEntry = false;
	private long timeStamp = 0;
	private double probability = 0;

	// ------------------------------------------------------	
	/**
	 * Creates a Barcode object from an array of ints.
	 * @param barNums the array of ints, 13 long
	 * @throws IllegalArgumentException if barNums is null.
	 * @throws IllegalArgumentException if barNums is not length 13.
	 * @throws IllegalArgumentException if an element of barNums is <0.
	 * @throws IllegalArgumentException if an element of barNums is >9.
	 */
	// ------------------------------------------------------
	public BarCode(int barNums[]) {
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
		timeStamp = System.currentTimeMillis();
		probability = 1;
	}
	// ------------------------------------------------------	
	/**
	 * Creates a Barcode object from a string.
	 * @param codeStr
	 * @throws IllegalArgumentException if String codeStr is null.
	 * @throws IllegalArgumentException if String codeStr is not length 13.
	 * @throws IllegalArgumentException if an element of codeStr is <0.
	 * @throws IllegalArgumentException if an element of codeStr is >9.
	 */
	// ------------------------------------------------------	
	public BarCode(String codeStr) {
		if (codeStr == null)
			throw new IllegalArgumentException("BarCode() code is null");
		if (codeStr.length() != BAR_CODE_LEN)
			throw new IllegalArgumentException("BarCode() codeStr " +
					"is wrong length = " + codeStr.length());
		char[] codeChars = codeStr.toCharArray();
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			barNums[i] = Integer.parseInt(codeStr.substring(i,i+1));
			if (barNums[i] < 0)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("BarCode() barNums[] has" +
						" element greater than 9 = " + barNums[i]);
			hasEntry = true;
		}
		timeStamp = System.currentTimeMillis();
		probability = 1;
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
	public boolean isValid() {
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
	// ------------------------------------------------------	
	/**
	 * Gets a numerical value for the digit in a barcode, note zero based.
	 * @param index the digit you want
	 * @throws IllegalArgumentException if index is out of bounds,
	 * 			expecting 0 =< index <=12.
	 * 
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
}