package selfCheckOut.hardWareInterface;
	/**
	 * This class is used to in the Hardware interface components of the 
	 * SelfChekcOut projectto contain a strip of potential barcode pixels.
	 * <p>
	 * @author Peter Gibney
	 * @version 23rd March 2008.
	 */
import selfCheckOut.hardWareInterface.*;

public class BarCodeStripe {

	private int startPix = 0;
	private int finishPix = 0;
	private int lineNum = 0;
	private int stripeLen = 0;
	private int startingPos = 0;
	private double unitBarWidth = 0;
	private double sigWhiteBlack = 0;
	private int startMidSpace = 0;
	private int endMidSpace = 0;
	private double centrePixD = 0d;
	private boolean parity = false; //we are odd for the moment
	private double[][] stripe = new double[HWIconst.ITEMS_PER_STRIP][2];
	private static int ODD_AND_EVEN = 0;
	private static int EVENS = 1;
	private static int ODDS = 2;
	// ------------------------------------------------------	
	/**
	 * Creates a BarCodeStripe object from an array run length information.
	 * @param startPos refers to the first bar/space in the stripe, 0 is the 
	 * left hand side space/bar
	 * @param lineNo is the line in the image that this stripe comes from
	 * @param scanLine is the array of run length information
	 * @throws IllegalArgumentException if scanLine is null.
	 * @throws IllegalArgumentException if scanLine.length <= 0.
	 * @throws IllegalArgumentException if an element of barNums is <0.
	 * @throws IllegalArgumentException if an element of barNums is >9.
	 */
	
	public BarCodeStripe(int startPos, int lineNo, int[][] scanLine) {
		if (scanLine == null) throw new 
			IllegalArgumentException("BarCodeStripe() scanLine[][] is null");
		if (scanLine.length <= 0) throw new 
			IllegalArgumentException("BarCodeStripe() scanLine.length <= 0");
		if (startPos < 0) throw new 
			IllegalArgumentException("BarCodeStripe() startPos < 0");
		
		assert startPos >= 0;
		
		if (lineNo < 0) throw new 
			IllegalArgumentException("BarCodeStripe() lineNo < 0");

		
		
		assert scanLine.length >0;
		assert startPos >= 0;
		lineNum = lineNo;
		startingPos = startPos;
		//make a copy of the relevant information as doubles
		for (int i = 0; i < HWIconst.ITEMS_PER_STRIP; i++) {
			stripe[i][0] = scanLine [i + startingPos][0]; //colour
			stripe[i][1] = scanLine [i + startingPos][1]; //length in pixels
		}
		//now find where this stripe exists in the raster line
		startPix = 0;
		for (int i = 0; i < startingPos; i++) {
			startPix = startPix + scanLine[i][1]; 
		}
		finishPix = 0; //wrt the first pixel in the screen
		for (int i = 0; i < startingPos + HWIconst.ITEMS_PER_STRIP ; i++) {
			finishPix = finishPix + scanLine[i][1]; 
			// this takes us up to the end of the last guard
		}
		finishPix = finishPix -1; //pvg 2 april 2008
		stripeLen = 1 + finishPix - startPix; //changed 2 april added 1? in PVG
		
		
		startMidSpace = 0;
		for (int i = 0; i < startingPos + 29; i++) { //29 = index for mid space
			startMidSpace = startMidSpace + scanLine[i][1]; 
		}
		endMidSpace = startMidSpace + scanLine[29+startingPos][1] - 1;
		//pixInMidSpace = scanLine[29][1];
		
		centrePixD = (endMidSpace + startMidSpace)/2d;
		
		unitBarWidth = ((double) stripeLen / (double) HWIconst.NUM_BAR_SPACE_UNITS);

		double sigBlackWidth = 0;
		for (int i = 0; i < HWIconst.NUM_GUARD_OFF_SETS; i = i+2) {
			sigBlackWidth = sigBlackWidth + stripe[HWIconst.GUARD_REF_LOCATIONS[i]][1];
		}
		double sigWhiteWidth = 0;
		for (int i = 1; i < HWIconst.NUM_GUARD_OFF_SETS; i = i+2) {
			sigWhiteWidth = sigWhiteWidth + stripe[HWIconst.GUARD_REF_LOCATIONS[i]][1];
		}
		
		double blackkAvg = 	sigBlackWidth / 6d;
		double whiteAvg = 	sigWhiteWidth / 5d;
	
		//double sigWhiteBlack = sigBlackWidth + sigWhiteWidth;
		sigWhiteBlack = sigBlackWidth + sigWhiteWidth;
		double avgWhiteBlack = sigWhiteBlack / 11d;
		double deltaBlack = 100*(avgWhiteBlack - blackkAvg);
		double deltaWhite = 100*(avgWhiteBlack - whiteAvg);
			
		// get here we have a (potential) code in the bars...
		//now apply the adaptive corrections
		for (int step = 0; step < stripe.length; step++) {
			stripe[step][1] = stripe[step][1]* 100;
			if (stripe[step][0] == 0) {
				stripe[step][1] = stripe[step][1] + deltaBlack;
			} else {
				stripe[step][1] = stripe[step][1] + deltaWhite;
			}
		}			
	}
	// ------------------------------------------------------
	/**
	 * Gets an array of doubles which is the width of each black and white
	 * bar in a digit encoding section of a barcode.
	 * @param blockNum the values for the digits
	 */	
	public double[] getNums(int blockNum) {
		assert blockNum >=0;
		int offSet;
		if (blockNum > 5) {
			//reading RHS
			offSet = 32 + ((blockNum-6) * 4); //32 beyond first guard
		} else {
			//reading LHS
			offSet = 3 + (blockNum * 4); //steps of 4 plus the 3 bands of the first quard
		}
		double[]blockInfo = new double[4];
		for (int j = 0; j < 4; j++) {
			blockInfo[j]= stripe[j+offSet][1];
		}
		return blockInfo;
	}
	// ------------------------------------------------------
	/**
	 * Returns the width of the guard bars and spaces.
	 */	

	public double getbarUnitWidth() {
		return unitBarWidth;
	}
	// ------------------------------------------------------	
	/**
	 * Returns the width of the barcode stripe in pixels.
	 */	
	public int getLength() {
		return stripeLen;
	}
	// ------------------------------------------------------
	/**
	 * Returns the line number in the picture scan where this 
	 * stripe was located.
	 */	
	public int getLineNum() {
		return lineNum;
	}
	// ------------------------------------------------------	
	/**
	 * Returns the starting pixel where this stripe begins
	 */	
	public int getStart() {
		return startPix;
	}
	// ------------------------------------------------------
	/**
	 * Returns the stopping pixel where this stripe begins
	 */	
	public int getEnd() { //reteurn the last pixel in the bar/space
		return finishPix;
	}
	// ------------------------------------------------------
	public int getStartMiddleSpace() {
		return startMidSpace;
	}
	// ------------------------------------------------------
	public int getEndMiddleSpace() {
		return endMidSpace;
	}
	// ------------------------------------------------------
	public double getCentrePos() {
		return centrePixD;
		//return (startPix + finishPix)/2d;
	}
	//--------------------------------------------------
	public BarNums decodeStripe() {
	assert stripe != null;
		Digit[] digits = null; //want to be able to return null
		boolean[] parityValues = new boolean[5];
		int method = ODD_AND_EVEN;
		Digit resultDigit = new Digit(method, this.getNums(0));
		if (resultDigit.isOdd()) {
			//we are scanning an object facing North = normal way
			digits = new Digit[13];//have something not null to return
			digits[1] = resultDigit; //the first read is the second
			for (int i = 2; i <= 12; i++) {
				if (i >= 7 )
					method = ODDS;
				resultDigit = new Digit(method, this.getNums(i-1));
				digits[i] = resultDigit;
				if (i < 7)
					parityValues[i - 2] = resultDigit.isEven();
			}
			resultDigit = new Digit(parityValues);
			digits[0] = resultDigit;
		} else {
			//double check that a there is not an error in the reading
			if (resultDigit.isEven()) {
				//we are scanning an object pointing South, ie upside down
				digits = new Digit[13];//have something not null to return
				digits[12] = resultDigit;// the first read is the last
				method = EVENS;
				for (int i = 11; i >= 1; i--) {
					if (i < 7 )
						method = ODD_AND_EVEN;
					resultDigit = new Digit(method, this.getNums(12 - i));
					digits[i] = resultDigit;
					if ((i < 7) && (i > 1))
						parityValues[i - 2] = resultDigit.isOdd();
				}
				resultDigit = new Digit(parityValues);
				digits[0] = resultDigit;
			} else {
				// error decoding digit
				// a three state boolean!!!
				System.out.println("***********Error reading parity of first stripe digit, val =  " + resultDigit.getDigit());
			}
		}
		//  could be null or ! null depending on if error decoding
		BarNums barNums = null;//want to be able to return null
		if (digits != null) {
			barNums = new BarNums(digits);
		}
		return barNums;
	}
	//--------------------------------------------------
}
