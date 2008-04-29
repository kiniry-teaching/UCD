package selfCheckOut.hardWareInterface;
import selfCheckOut.*;

/**
 * This class is used to gather up a collection of barcodes and to vote
 * which is the most likely based on frequency, for development purposes it
 * can output a list of digits and frequency.
 * <p>
 * 
 * @author Peter Gibney
 */


public class TentativeNumbers {

	private int[][] tentativeNumbers = new int[13][22]; 
	// position 1..13, digits 0..19 & bad = [10], weights 
	private double[][] sumProbabilities = new double[13][20];
	private boolean hasTents = false;
	//-----------------------------------------------------------------------
	public TentativeNumbers() {
		for (int i = 0; i < 13; i++) {
			for (int j = 0; j < 22; j++) {
				tentativeNumbers[i][j] = 0;
			}
			for (int j = 0; j < 20; j++) {
				sumProbabilities[i][j] = 0d;
			}
		}
	}
	// ------------------------------------------------------
	public void addToTentative(BarNums inNums) {
		assert inNums != null;
		assert inNums.hasDigits() >0;
		int[] code = inNums.getNumbers(false);
		hasTents = true;
		double[] probs = inNums. getProbabilities();
		int weight = getNumsWeight(code);
		for (int pos = 0; pos < 13; pos++) {
			assert code[pos] <= 20;
			assert code[pos] >= -1;
			if (code[pos] >= 0) {
				tentativeNumbers[pos][code[pos]]+=weight; // increment the count
				sumProbabilities [pos][code[pos]]+=
					((double)weight * probs[pos]);
			
			} else { // bad digit, put info in [10] must be -1
				assert code[pos] == -1;
				tentativeNumbers[pos][20]+=weight; // increment the frequency
			}
			tentativeNumbers[pos][21]+= weight; // increment the total
		}
	}
	// ------------------------------------------------------
	public boolean hasTents() {
		return hasTents;
	}
	// ------------------------------------------------------

	public void showTentative() {
		// tentativeNumbers = new int[13][11]; // position 1..13, digits 0..9; note unknown is kept in [10],  weight / frequency 
		System.out.println("\nnumbers discovered\n");
		System.out.print("B:  ");
		// print the barcode positions 1..13 left to right
		for (int pos = 1; pos <= 13; pos++) {
			System.out.print(HWIHelper.padIntToString(pos, 4) + " ");
		}
		System.out.print("\n");
		for (int num = 0; num < 20; num++) {
			System.out.print(HWIHelper.padIntToString(num,2) + ": ");
			for (int pos = 0; pos < 13; pos++) {
				System.out.print(HWIHelper.padIntToString(tentativeNumbers[pos][num], 4) + " ");
			}
			System.out.print("\n");
		}
		System.out.print("?:  ");
		// print the number of wild card entries
		for (int pos = 0; pos < 13; pos++) {
			System.out.print(HWIHelper.padIntToString(tentativeNumbers[pos][20], 4) + " ");
		}
		System.out.print("\n");
		
		System.out.print("\nN:  ");
		// print the total number of entries
		for (int pos = 0; pos < 13; pos++) {
			System.out.print(HWIHelper.padIntToString(tentativeNumbers[pos][21], 4) + " ");
		}
		System.out.print("\n\nV': ");
		// print the most frequent occurring value
		for (int pos = 0; pos < 13; pos++) {
			int value = mostFreq(0, 19, tentativeNumbers[pos]);
			if (value == -1) {
				System.out.print("   ? ");
			} else {
				System.out.print(HWIHelper.padIntToString(value, 4) + " ");
			}
		}
		System.out.print("\n\nV:  ");
		// print the most frequent occurring value
		for (int pos = 0; pos < 13; pos++) {
			int value = mostFreq(0, 19, tentativeNumbers[pos]);
			if (value == -1) {
				System.out.print("   ? ");
			} else {
				System.out.print(HWIHelper.padIntToString(value%10, 4) + " ");
			}
		}
		System.out.println("\n\n");
	}
	// ------------------------------------------------------
	public BarCode assembleBarCode(Long timeStamp) {
		BarCode retCode = null;
		int[] codeNumbers = new int[13];
		double[] barProbs = new double[13];
		for (int pos = 0; pos < 13; pos++) {
			int index = mostFreq(0, 19, pos);
			codeNumbers[pos] = mostFreq(0, 19, tentativeNumbers[pos]); // get the most freq in the column of numbers
			assert codeNumbers[pos] == index;//mostFreq(0, 19, pos);
			codeNumbers[pos] = codeNumbers[pos]%10; //strip off the parity info
			if (index >=0) {
				barProbs[pos] = 
					(sumProbabilities[pos][index]/(double)tentativeNumbers[pos][21]);
			} else {
				barProbs[pos] = 1d;
			}
		}
		if (isValid(codeNumbers))
			retCode = new BarCode(codeNumbers, barProbs, timeStamp);
		return retCode;
	}
	//----------------------------------------------------
	private boolean isValid(int[] numbers) {
		assert numbers != null;
		assert numbers.length ==13;
		int[] tempNums = new int[13];
		boolean valid = true; //assume is valid
		for (int i = 0; i<13; i++) {
			if (numbers[i] == -1) {
				valid = false;
				if (HWIconst.DE_BUG)
					System.out.println("Failed valid, i = " + i + ", num = " + numbers[i]);
			}
			tempNums[i] = numbers[i] %10;
		}
		if (valid) {
			// calculate the checksum of the barcode:
			int checkSum = tempNums[0] + tempNums[2] + tempNums[4] + 
				tempNums[6] + tempNums[8] + tempNums[10] + 
				(3*(tempNums[1] + tempNums[3] + tempNums[5] + 
				tempNums[7] + tempNums[9] + tempNums[11]));
			int checkSumValue = 10 - (checkSum % 10);
			if (checkSumValue == 10)
				checkSumValue = 0;
			valid = (tempNums[12] == checkSumValue);

			if (HWIconst.DE_BUG) {
				System.out.print("CHECK:");
				for (int i = 0; i < 13; i++) System.out.print(" " + numbers[i] + " " + tempNums[i] );
					System.out.println("  checkSumValue:" + checkSumValue);
			}
		}
		return valid;
	}
	// ------------------------------------------------------
	private int mostFreq(int start, int stop, int[] list) {
		assert list != null;
		assert list.length > 0;
		assert start >= 0;
		assert stop >=0;
		assert stop >= start;
		int freq = -1;
		int value = -1;
		for (int pos = start; pos <= stop; pos++) {
			if (list[pos] >= freq) {
				freq = list[pos];
				value = pos;
			}
		}
		if (freq == 0) // no occurrance so return a wild card
			value = -1;
		return value;
	}
	// ------------------------------------------------------
	private int mostFreq(int start, int stop, int column) {
		assert column >=0;
		assert column <=12;
		int[] list = tentativeNumbers[column];
		int freq = -1;
		int value = -1;
		for (int pos = start; pos <= stop; pos++) {
			if (list[pos] >= freq) {
				freq = list[pos];
				value = pos;
			}
		}
		if (freq == 0) { // no occurrance so return a wild card
			value = -1;
		}
		return value;
	}
	// ------------------------------------------------------

	private int getNumsWeight(int[] nums) {
		assert nums != null;
		assert nums.length == 13;
		int numCnt = 0;
		int weight = 0;
		for (int i = 0; i < 13; i++) {
			if (nums[i] >=0)
				numCnt++;
		}
		if (numCnt == 13){
			if (isValid(nums)) {
				weight = numCnt*2;
			} else {
				weight = numCnt;
			}
		} else {
			weight = numCnt;
		}
		return weight;
	}
	//--------------------------------------------------
	
}
