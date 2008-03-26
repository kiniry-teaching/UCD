	/**
	 * This  class is used to hold an array of ints for use in the 
	 * fabrication of a Barcode in the barcode reader, 
	 * for the SelfChekcOut project.
	 * <p>
	 * 
	 * @author Peter Gibney
	 * @version 25th March 2008.
	 */

public class BarNums {
	private static final int BAR_CODE_LEN = 13;
	private int[] barNums = new int[BAR_CODE_LEN];
	private boolean hasEntry = false;
	// ------------------------------------------------------	
	/**
	 * Creates a BarNums object from an array of ints.
	 * @param barNums the array of ints, 13 long
	 * @throws IllegalArgumentException if barNums is null.
	 * @throws IllegalArgumentException if barNums is not length 13.
	 */
	// ------------------------------------------------------
	public BarNums(int barNums[]) {
		if (barNums == null)
			throw new IllegalArgumentException("BarNums() barNums[] is null");
		if (barNums.length != BAR_CODE_LEN)
			throw new IllegalArgumentException("BarNums() barNums[] " +
					"is wrong length = " + barNums.length);
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			this.barNums[i] = barNums[i];
			if (this.barNums[i] >= 0)
				hasEntry = true;
		}
	}
	// ------------------------------------------------
	/**
	 * Converts this BarNums object to a String.
	 * 
	 * @return this Code as a String.
	 */
	// ---------------------------------------------------------
	public String toString() {
		String str = "";
		for (int i = 0; i < BAR_CODE_LEN; i++) {
			if (barNums[i] >= 0) {
				str = str + barNums[i] + ".";
			} else {
				str = str + "?" + ".";
			}
		}
		return str;
	}
	// --------------------------------------------------------------------
	public boolean isEntryFull() {
		boolean full = true; // assume full
		if (hasEntry) {
			for (int i = 0; i < BAR_CODE_LEN; i++) {
				if (barNums[i] < 0) {
					full = false;
					break; // will be false
				}
			}
		} else {
			full = false;
		}
		return full;
	}
	// -------------------------------------------------------------
	/**
	 * Checks if the BarNums is a valid.
	 * 
	 * @return true, if the code is valid.
	 */
	// --------------------------------------------------
	public boolean isValid(boolean stripParity) {
		boolean valid = false; // assume not valid
		if (isEntryFull()) {
			int[] checkNums = getNumbers(stripParity);
			// calculate the checksum of the barcode:
			int checkSum = checkNums[0] + checkNums[2] + checkNums[4] + 
							checkNums[6] + checkNums[8] + checkNums[10] + 
							(3*(checkNums[1] + checkNums[3] + checkNums[5] + 
							checkNums[7] + checkNums[9] + checkNums[11]));
			int checkSumValue = 10 - (checkSum % 10);
			if (checkSumValue == 10)
				checkSumValue = 0;
			valid = (barNums[12] == checkSumValue);
		}
		return valid;
	}
	// ----------------------------------------------------
	public boolean hasEntry() {
		return hasEntry;
	}
	// ---------------------------------------------
	public int[] getNumbers(boolean stripParity) {
		int[] retNums = new int[BAR_CODE_LEN]; 
		for (int i= 0; i<BAR_CODE_LEN;i++){
			if ((barNums[i] > 0) && stripParity) {
				retNums[i] = barNums[i]%10;
			} else {
				retNums[i] = barNums[i];
			}
		}
		return retNums;
	}
	// ----------------------------------------------------------
	public int getCheckDigit(boolean stripParity) {
		int retInt = barNums[12];
		if ((retInt > 0) && stripParity) {
			retInt = retInt%10;
		}
		return retInt;
	}
	// ------------------------------------------------------	
	/**
	 * Gets a numerical value for the digit in a BarNums, note zero based.
	 * @param index the digit you want
	 * @throws IllegalArgumentException if index is out of bounds,
	 * 			expecting 0 =< index <=12.
	 */
	// ---------------------------------------------
	public int getNumber(int index, boolean stripParity) {
		if ((index >= 12) || (index <= 0)) 
			throw new IllegalArgumentException("BarNums.getNumber() passed " +
					"illegal argument index = " + index + 
					", expecting: 0 <= index <= 12");
		int retInt = barNums[index];
		if ((retInt > 0) && stripParity) 
			retInt = retInt%10;
		return retInt;
	}
} //end class
