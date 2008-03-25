	/**
	 * This  class is used to hold a Barcode for the SelfChekcOut project.
	 * <p>
	 * 
	 * @author Peter Gibney
	 * @version 23rd March 2008.
	 */
public class Barcode {

	private int[] barNums = new int[13];
	private boolean hasEntry = false;
	// ------------------------------------------------------
	public Barcode(int barNums[]) {
		if (barNums == null)
			throw new IllegalArgumentException("Barcode() barNums[] is null");
		if (barNums.length != 13)
			throw new IllegalArgumentException("Barcode() barNums[] " +
					"is wrong length = " + barNums.length);
		for (int i = 0; i < 13; i++)
			this.barNums[i] = -1;
		for (int i = 0; i < 13; i++) {
			this.barNums[i] = barNums[i];
			if (barNums[i] < 0)
				throw new IllegalArgumentException("Barcode() barNums[] has" +
						" element less than 0 = " + barNums[i]);
			if (barNums[i] > 9)
				throw new IllegalArgumentException("Barcode() barNums[] has" +
						" element greater than 10 = " + barNums[i]);
			if (this.barNums[i] >= 0)
				hasEntry = true;
		}
	}
	// ------------------------------------------------------	
	/**
	 * Creates a Barcode object from a string.
	 * @param code
	 * @throws IllegalArgumentException if String code is null.
	 * @throws IllegalArgumentException if String code is not length 13.
	 * @throws IllegalArgumentException if an element of code is <0.
	 * @throws IllegalArgumentException if an element of code is >9.
	 */
	// ------------------------------------------------------	
	public Barcode(String code) {
		if (code == null)
			throw new IllegalArgumentException("Barcode() code is null");
		if (code.length() != 13)
			throw new IllegalArgumentException("Barcode() code " +
					"is wrong length = " + code.length());
		for (int i = 0; i < 13; i++)
			this.barNums[i] = -1;
		if (code.length() == 13) {
			char[] codeChars = code.toCharArray();
			for (int i = 0; i < 13; i++) {
				this.barNums[i] = 
					Integer.valueOf("" + codeChars[i]).intValue();
				if (barNums[i] < 0)
					throw new IllegalArgumentException("Barcode() barNums[] has" +
							" element less than 0 = " + barNums[i]);
				if (barNums[i] > 9)
					throw new IllegalArgumentException("Barcode() barNums[] has" +
							" element greater than 9 = " + barNums[i]);
				if (this.barNums[i] >= 0)
					hasEntry = true;
			}
		}
	}
	// ------------------------------------------------
	/**
	 * Converts this Barcode object to a String.
	 * 
	 * @return this Code as a String.
	 */
	// ---------------------------------------------------------
	public String toString() {
		String s = "";
		for (int i = 0; i < barNums.length; i++) {
			assert barNums[i] >= -1;
			assert barNums[i] <= 9;
			if (barNums[i] >= 0) {
				s = s + barNums[i] + "";
			} else {
				s = s + "?";
			}
		}
		return s;
	}
	// --------------------------------------------------------------------
	public boolean isEntryFull() {
		boolean full = true; // assume full
		if (hasEntry) {
			for (int i = 0; i < barNums.length; i++) {
				if ((barNums[i] < 0) || (barNums[i] > 9)) {
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
	 * Checks if the barcode is a valid.
	 * 
	 * @return true, if the code is valid.
	 */
	// --------------------------------------------------
	public boolean isValid() {
		boolean valid = false; // assume not valid
		if (isEntryFull()) {
			// calculate the checksum of the barcode:
			int checkSum = barNums[0] + barNums[2] + barNums[4] + 
							barNums[6] + barNums[8] + barNums[10] + 
							(3*(barNums[1] + barNums[3] + barNums[5] + 
							barNums[7] + barNums[9] + barNums[11]));
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
	public int[] getNumbers() {
		int[] retNums = new int[13]; 
		for (int i= 0; i<13;i++){
			retNums[i] = barNums[i];
		}
		return retNums;
	}
	// ----------------------------------------------------------
	public int getCheckDigit() {
		return barNums[12];
	}
	// ---------------------------------------------
	public int getNumber(int index) {
		assert (index >=0);
		assert (index <=12);
		int retValue = -1;// assume bad index
		if ((index >= 0) && (index <= 12))
			retValue = barNums[index];
		return retValue;
	}
}