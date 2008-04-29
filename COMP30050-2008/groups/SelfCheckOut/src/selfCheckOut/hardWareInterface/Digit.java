package selfCheckOut.hardWareInterface;
/**
 * This class is used to decode a digit from a barcode 
 * for the Hardware interface 
 * components of the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 */
public class Digit {

private static final int ODD_AND_EVEN = 0;
private static final int EVENS = 1;
private static final int ODDS = 2;

private static final double[][] KEY_CODES = 	
			{{300, 200, 100, 100},
			{200, 200, 200, 100},
			{200, 100, 200, 200},
			{100, 400, 100, 100},
			{100, 100, 300, 200},
			{100, 200, 300, 100},
			{100, 100, 100, 400},
			{100, 300, 100, 200},
			{100, 200, 100, 300},
			{300, 100, 100, 200},
			{100, 100, 200, 300},
			{100, 200, 200, 200},
			{200, 200, 100, 200},
			{100, 100, 400, 100},
			{200, 300, 100, 100},
			{100, 300, 200, 100},
			{400, 100, 100, 100},
			{200, 100, 300, 100},
			{300, 100, 200, 100},
			{200, 100, 100, 300}};


private static final boolean[][] FIRST_DIGIT_LIST =
	{{ false, false, false, false, false },
	{false, true, false, true, true },
	{false, true, true, false, true },
	{false, true, true, true, false },
	{true, false, false, true, true },
	{true, true, false, false, true },
	{true, true, true, false, false },
	{true, false, true, false, true },
	{true, false, true, true, false },
	{true, true, false, true, false }};



private int parity; //odd = -1, NA = 0, even = 1
private int digit;
private boolean objectParityType; //true for created from run length
							//false for created from parity codes
double probability = 1d;
//---------------------------------------------------------------
/**
 * Constructs a Digit object from a run length encoded array of 
 * bars and spaces.
 * @param codeTable Which code table to use, 0 to use odd and even, 
 * 1 to use even, 2 to use odd.
 * @param bars the run length coding of bars and spaces in an 
 * array of doubles, length 4.
 * @throws IllegalArgumentException if bars is null.
 * @throws IllegalArgumentException if length of bars is not 4.
 * @throws IllegalArgumentException if codeTable is  < 0.
 * @throws IllegalArgumentException if codeTable is  > 2.
 */
public Digit(int codeTable, double[] bars) {
	if (bars == null)
		throw new IllegalArgumentException("Digit() bars is null");
	if (bars.length != 4)
		throw new IllegalArgumentException("Digit() bars " +
				"is wrong length = " + bars.length + 
				", expecting length = 4");
	if (codeTable < 0)
		throw new IllegalArgumentException("Digit() codeTable value too " +
			"small= " + codeTable + ", expecting: 0<= codeTable <= 2 ");

	if (codeTable > 2)
		throw new IllegalArgumentException("Digit() codeTable value too " +
			"large= " + codeTable + ", expecting: 0<= codeTable <= 2 ");
	double maxDiffValue = 0d;
	int start = 0; //where we read in the table
	int end = 0; //finish reading
	int offSet = 0;
	double[] normedCode = normalizeVector(bars);
	// print some debugging information:
	if (HWIconst.DE_BUG) {
		System.out.println("Recognize Number (code table to use: " + codeTable + "):");
		System.out.println("lengths: " + bars[0] + " " + bars[1] + " " + bars[2]+ " " + bars[3]);
		System.out.println("normed lengths: " + normedCode[0] + " " + normedCode[1] + " " + normedCode[2] + " " + normedCode[3]);
	}
	// try to detect the digit that is encoded by the set of four normed bar lenghts:
	double maxDiff = 960d * 960d;
	double minDiff = Double.MAX_VALUE;
	int minDiffPos = 0;
	start = 0;
	end = 0;
	if (codeTable == ODD_AND_EVEN) {
		start = 0;
		end = 19;
		offSet = 0;
	}
	if (codeTable == ODDS) {
		start = 0;
		end = 9;
		offSet = 0;
	}
	if (codeTable == EVENS) {
		start = 10;
		end = 19; //end on this number
		offSet = 10;
	}
	double[] Diffs = new double[(end - start) + 1];
	double sumDiffs = 0d;
	for (int i = start; i <= end; i++) {
		Diffs[i-offSet] = euclidDistSquared(normedCode, KEY_CODES[i]);;
		sumDiffs = sumDiffs + Diffs[i-offSet];
		maxDiffValue = Math.max(maxDiffValue, Diffs[i-offSet]);
		if (Diffs[i-offSet] < minDiff) {
			minDiff = Diffs[i-offSet];
			minDiffPos = i;
		}
	}
	if ((minDiff > maxDiff) || 
			minHasTies(start, end, offSet, minDiffPos, Diffs)) {
		probability = 1d;
		digit = -1;
		parity = 0; //odd = -1, NA = 0, even = 1
	} else {
		//probability = 1d - (minDiff/sumDiffs);
		probability = Math.pow(1d - (minDiff/maxDiffValue),2);
		digit = minDiffPos;
		if (minDiffPos < 10) {
			parity = -1; //odd = -1, NA = 0, even = 1
		} else {
			parity = 1; //odd = -1, NA = 0, even = 1
		}
	}
	if (HWIconst.DE_BUG)
		System.out.println("maxDiffValue = " + maxDiffValue);
	objectParityType = false;
}
//---------------------------------------------------------------
private double euclidDistSquared(double[] inVector, double[] keyCodes) {
	double temp = 0d;
	for (int i = 0; i < 4; i++) {
		temp = temp + Math.pow((inVector[i] - keyCodes[i]), 2);
	}
	assert temp >= 0;
	return temp;
}
//---------------------------------------------------------------
// normalize the run code so that the total length is 700
private double[] normalizeVector(double[] inVector) {
	double[]  temp = new double[4];
	double initLen = 0;
	for (int i = 0; i < 4; i++) {
		initLen = initLen + inVector[i];
	}
	for (int i = 0; i < 4; i++) {
		temp[i] = ((inVector[i]/initLen) * 700);
	}
	return temp;
}
//---------------------------------------------------------------
//crawl through the array looking for ties
private boolean minHasTies(int startPos, 
							int endPos,
							int offSet,
							int minLocation,
							double[] Diffs) {
	double minDiff = Diffs[minLocation-offSet];
	boolean tie = false; //assume no ties
	for (int i = startPos; i <= endPos; i++) {
		if (i != minLocation) {
			//not looking at self
			if (Diffs[i-offSet] == minDiff) {
				tie = true;
				if (HWIconst.DE_BUG)
					System.out.println("Tie; i=" + i + ", start = " + startPos + 
						", end= " + endPos + ", minDiffPos=" + minLocation +
						", offSet = " + offSet + ", minDiff= " + minDiff);
			}
		}
	}
	return tie;
}
//---------------------------------------------------------------
/**
 * Constructs a Digit object from an array of booleans.
 * @param parityValues The array of booleans, length 5 which is used to 
 * create the first digit from the parity of digits 3 to 7.
 * @throws IllegalArgumentException if parityValues is null.
 * @throws IllegalArgumentException if length of parityValues is not 5.
 */
public  Digit(boolean[] parityValues) {
	if (parityValues == null)
		throw new IllegalArgumentException("Digit() parityValues is null");
	if (parityValues.length != 5)
		throw new IllegalArgumentException("Digit() parityValues " +
				"is wrong length = " + parityValues.length + 
				", expecting length = 5");
	// search for a matching parity
	boolean found = false;
	int i = 0;
	while (!found && i < 10){ 
		found = true;
		int j = 0;
		while (found && j < 5) {
			found = found && parityValues[j] == FIRST_DIGIT_LIST[i][j];
			j++;
		}
		//if found is true here then we have got a match
		i++;
	}
	if (found) {
		digit = i-1;
		parity = 0; //odd = -1, NA = 0, even = 1
	} else {
		parity = 0; //odd = -1, NA = 0, even = 1
		digit = -1;
	}
	objectParityType = true;
}
//------------------------------------------------------------------------------	
public int getDigit() {
	return digit;
}
// ------------------------------------------------------
public boolean isEven() {
	if (objectParityType)
		throw new UnsupportedOperationException("Digit.isEven() is not " +
				"supported on an object constructed from parity values.");
	return (parity == 1); //odd = -1, NA = 0, even = 1
}
// ------------------------------------------------------
public boolean isOdd() {
	if (objectParityType)
		throw new UnsupportedOperationException("Digit.isEven() is not " +
				"supported on an object constructed from parity values.");
	return (parity == -1); //odd = -1, NA = 0, even = 1
}
// ------------------------------------------------------
public double getProbability() {
	return probability;
}
// ------------------------------------------------------
public boolean hasNoParity() {
	if (objectParityType)
		throw new UnsupportedOperationException("Digit.isEven() is not " +
				"supported on an object constructed from parity values.");
	return (parity == 0); //odd = -1, NA = 0, even = 1
}
// ---------------------------------
/**
 * Converts this Digit object to a String.
 * 
 * @return this Code as a String.
 */
// ----------------------------------------
public String toString() {
	String s = "Digit= " + digit + ", parity = " + parity + ", [odd = -1, NA = 0, even = 1]";
	return s;
}
// --------------------------------------------------
}
