package selfCheckOut.hardWareInterface;
/**
 * This class is used to to create a list of stripes from the scanned
 * image, it searches for a potential code in each scan line using the widths
 * of white and black to judge/estimate whether a code is present.
 * <p>
 * 
 * @author Peter Gibney
 */

import java.awt.image.*;
import java.awt.*;
public class Striper {
	
	private BarCodeStripe[] stripes = null;
	private int startIm;
	private int stopIm;
	private Runner[] theRuns = null;
	private int theRunsSize = 0;
	private int runsCount = 0;
	private int theStripesSize = 0;
	private int stripesCount = 0;
	
	
	public Striper(ImageMaker imaker, int selection) {
		if (selection == 7) {
			theStripesSize = 7 * 800;
			theRunsSize = 7 * 480;
			startIm = 0;
			stopIm = 7;
		} else {
			theStripesSize = 800;
			theRunsSize = 480;
			startIm = selection;
			stopIm = selection+1;
		}
		stripes = new BarCodeStripe[theStripesSize];
		theRuns = new Runner[theRunsSize];
		int[] ScanScope = new int[640]; // matrix for screen grab processing.
		for (int i = startIm; i < stopIm; i++) {
			BufferedImage binImage = imaker.getBinaryImage(i);
			int sizeX = binImage.getWidth();
			int sizeY = binImage.getHeight();
			for (int y = 0; y < sizeY; y++) {
				for (int x = 0; x < sizeX; x++) {
					int pixel = binImage.getRGB(x, y);
					Color pixelColour = new Color(pixel, false);
					int greyCol = (pixelColour.getBlue());
					ScanScope[x] = greyCol;
				}
				Runner tempRunner = new Runner(ScanScope, y);
				if (tempRunner.getLength() >= 59) {
					theRuns[runsCount] = tempRunner;
					runsCount++;
				}
			}
			if (HWIconst.DE_BUG) {
				System.out.println("MAKING RUNS>>>>>>>>>>>>: image = " + i + 
						", runs = "  + runsCount);
			}
		}
		if (HWIconst.DE_BUG) {
			System.out.println("MADE RUNS>>>>>>>>>>>> " + runsCount);
		}
	}
	//----------------------------------------------------------------
	public BarCodeStripe getStripe(int selection) {
		assert selection >=0;
		assert selection < stripes.length;
		return stripes[selection];
	}
	//----------------------------------------------------------------
	public int getNumRuns() {
		return runsCount;
	}
	//----------------------------------------------------------------
	public void makeStripes() {
		for (int i = 0; i <runsCount; i++ ) {
			Runner tempRunner = theRuns[i];
			BarCodeStripe tempStripe = getStripe(tempRunner.getRunner(), 0, 
					tempRunner.getLength(), tempRunner.getLineNo());
			if (HWIconst.DE_BUG) {
				System.out.println("MAKING STRIPES>>>>>>>>>>>>> " + 
						stripesCount);
			}
			if (tempStripe != null) {
				stripes[stripesCount] = tempStripe;
				stripesCount++;
			}
		}
		if (HWIconst.DE_BUG) {
			System.out.println("makeStripes() runsCount = " + 
					runsCount + ", stripesCount= " + stripesCount);
		}
	}
	//----------------------------------------------------------------
	public int getNumStripes() {
		return stripesCount;
	}
	//----------------------------------------------------------------
	public BarCodeStripe[] getStripes() {
		BarCodeStripe[] tempStripes = null;
		if (stripesCount > 0) {
			tempStripes = new BarCodeStripe[stripesCount];
			for (int i = 0; i < stripesCount; i++) {
				tempStripes[i] = stripes[i];
			}
		}
		return tempStripes;
	}
	//-------------------------------------------------------------------------
	private BarCodeStripe getStripe(int[][] bars, int startPos, 
										int endPos, int lineNo) {
		assert bars != null;
		assert (bars.length >0);
		assert (startPos >=0);
		assert (endPos >=0);
		assert (startPos <=endPos);
		// determine the length of the path in pixels
		int leftGuardStart;
		// if present get position of the start guard
		leftGuardStart = 0;
		if (bars[startPos][0] ==HWIconst.BINARY_WHITE) //want to start looking at black 
				startPos++;			//move to next position if initially white
									// this means that we can crawl through the line in steps of 2
		boolean foundGuard = false;
		int index = startPos;
		BarCodeStripe barCodeStripe = null;
		while (!foundGuard && (index < endPos - 58)) {
			if (checkCandidateGuards(bars, index)) { // check the black starting bar
				//found a suitable strip
				leftGuardStart = index;
				barCodeStripe = new BarCodeStripe(leftGuardStart, lineNo, bars);
				foundGuard = true;
			}
			index=index+2; //note steps of 2
		}
		return barCodeStripe;
	}
	//--------------------------------------
	private boolean checkBalancedLengths(int[][] bars, int startLocation) {
		assert startLocation >=0;
		assert startLocation <= bars.length - HWIconst.ITEMS_PER_STRIP;
		assert bars != null;
		boolean guardOK = true;  //assume good
		//going to check if we are length balanced about the middle guards
		int sigmaLeft = 0; // the total len of all the left data elements
		for (int posCheck = startLocation + HWIconst.START_LEFT_GROUP; 
			posCheck <= (HWIconst.END_LEFT_GROUP + startLocation); 
			posCheck++) {
			//note the loop guard {<=} as we want to include the last 
			sigmaLeft = sigmaLeft + bars[posCheck][1];
		}
		int sigmaRight = 0; // the total len of all the right data elements
		for (int posCheck = startLocation + HWIconst.START_RIGHT_GROUP; 
			posCheck <= (HWIconst.END_RIGHT_GROUP + startLocation); 
			posCheck++) {
			//note the loop guard {<=} as we want to include the last 
			sigmaRight = sigmaRight + bars[posCheck][1];
		}
		//want to avoid divide by zero or close to it
		double numerator = (double)Math.min(sigmaRight, sigmaLeft);  
		double denominator = (double)Math.max(sigmaRight, sigmaLeft);  
		
		guardOK = numerator/denominator >= 0.80; //0.95
		if (!guardOK && HWIconst.DE_BUG_FILTERING) {
		System.out.println("Eliminated due to non centering. " + sigmaLeft + 
				", " + sigmaRight + ", unit=" + bars[startLocation][1] +
				", & unit=" + bars[startLocation +1][1] + ", rati=" +
				numerator/denominator);
		}
		return guardOK;
	}
	//--------------------------------------
	private boolean checkGuardWidthsInRange(int[][] bars, int startLocation) {
		assert startLocation >=0;
		assert startLocation <= bars.length - HWIconst.ITEMS_PER_STRIP;
		assert bars != null;
		boolean guardOK = true;  //assume good
		int loopPos = 0;
		//check it guard widths are in range
		while (guardOK && loopPos < (HWIconst.NUM_GUARD_OFF_SETS)) {
			int posOffset = HWIconst.GUARD_REF_LOCATIONS[loopPos];
			int posLocation = posOffset + startLocation;
			guardOK = // check that the guard element is not too narrow
				(guardOK && (bars[posLocation][1] >= HWIconst.MIN_UNIT_WIDTH));
			guardOK = // check that the guard element is not too wide
				(guardOK && (bars[posLocation][1] <= HWIconst.MAX_UNIT_WIDTH));
			loopPos++;
		}
		if (!guardOK && HWIconst.DE_BUG_FILTERING)
			System.out.println("Eliminated due to out of tolerance guard widths");
		return guardOK;
	}
	//--------------------------------------
	private boolean checkGuardWidthsDifference(int[][] bars, int startLocation) {
		assert startLocation >=0;
		assert startLocation <= bars.length - HWIconst.ITEMS_PER_STRIP;
		assert bars != null;
		boolean guardOK = true;  //assume good
		// check that the guard element width diffs are not too great
		int loopPosOuter = 0;
		while (guardOK && loopPosOuter < (HWIconst.NUM_GUARD_OFF_SETS -1)) { //inner loop will check last element
			int posOffsetOuter = HWIconst.GUARD_REF_LOCATIONS[loopPosOuter];
			int posLocationOuter = posOffsetOuter + startLocation;
			int loopPosInner = loopPosOuter + 1; //examine the offset to the right
			while (guardOK && loopPosInner < (HWIconst.NUM_GUARD_OFF_SETS)) {
				int posOffsetInner = HWIconst.GUARD_REF_LOCATIONS[loopPosInner];
				int posLocationInner = posOffsetInner + startLocation;
				guardOK = // check that the guard element width diffs are not too great
					(Math.abs(bars[posLocationOuter][1] - bars[posLocationInner][1]) <= HWIconst.MAX_GUARD_ELEMENT_WIDTH);
				loopPosInner++;
			} // end inner loop
			loopPosOuter++;
		} //end outer loop
		if (!guardOK && HWIconst.DE_BUG_FILTERING)
			System.out.println("Eliminated due to out of tolerance guard difference widths");
		return guardOK;
	}
	//--------------------------------------

	private boolean checkCandidateGuards(int[][] bars, int startLocation ){
		assert startLocation >=0;
		assert startLocation <= bars.length - HWIconst.ITEMS_PER_STRIP;
		assert bars != null;

		assert bars[startLocation][0] == 0; //make sure we are on black
		boolean guardOK = (bars[startLocation][0] == 0);  //check that we start with a black
		guardOK = guardOK && checkGuardWidthsInRange(bars, startLocation);
		guardOK = guardOK && checkGuardWidthsDifference(bars, startLocation); 
		
		
		
		if (guardOK) {	
			//calculate the standard deviation and mean of guard black & white
			double sigmaLength = 0; // the total len of all the elements in the guards
			double sigmaLenSqrd = 0; // the total len of all the squaredelements in the guards
			for (int guardCheck = 0; guardCheck < HWIconst.NUM_GUARD_OFF_SETS; guardCheck++) {
				double guardLen = 
				bars[startLocation + HWIconst.GUARD_REF_LOCATIONS[guardCheck]][1];
				sigmaLength = sigmaLength + guardLen;
				sigmaLenSqrd = sigmaLenSqrd + (guardLen * guardLen);
			}
			double stdDev = 0;
			double meanLen = 0;
			meanLen = (double)(sigmaLength/(double)HWIconst.NUM_GUARD_OFF_SETS);
			stdDev = Math.sqrt((sigmaLenSqrd / (double)HWIconst.NUM_GUARD_OFF_SETS)
						- (meanLen * meanLen));

			//now measure the length in pixels
			int pixLen = 0; //to measure the length in pixels in the proposed barcode strip
			for (int barCheck = startLocation; 
				barCheck < (startLocation + HWIconst.ITEMS_PER_STRIP); 
				barCheck++) {
			pixLen = pixLen + bars[barCheck][1]; 
			// count the actual pixels
			}
			//now check if the actual length is in accordance with the mean length
			guardOK = (guardOK && 
						((meanLen * (double)HWIconst.NUM_BAR_SPACE_UNITS) > 
						(((double)pixLen) / HWIconst.SCAN_LEN_TOLERANCE))); 
		
			guardOK = (guardOK && 
						((meanLen * (double)HWIconst.NUM_BAR_SPACE_UNITS) < 
						((double)pixLen) * HWIconst.SCAN_LEN_TOLERANCE));
		
			/* */
			if (!guardOK && HWIconst.DE_BUG_FILTERING)
				System.out.println("Eliminated due to inconsistent " +
								"expected and observed length of strip, " +
								"exp= " 
								+ (meanLen*(double)HWIconst.NUM_BAR_SPACE_UNITS)
								+ ", actual = " + pixLen + ", mean = " +
								meanLen + 
								".");
			 /* */
		
			if (guardOK) { 
				//now check the variation of the guard widths
				guardOK = (guardOK && (stdDev/meanLen <= HWIconst.SCAN_BAR_VAR));
		
				/* */	
				if (!guardOK && HWIconst.DE_BUG_FILTERING)
					System.out.println("Eliminated due to excessive variation " +
					"in the guards, PixLen= " + pixLen +
					", stdDev = " +  stdDev + 
					", tol = " + HWIconst.SCAN_BAR_VAR + 
					", Mean= " + meanLen);
				 /* */
			}
		}
		guardOK = guardOK && checkBalancedLengths(bars, startLocation);
		//guardOK = true;
		return guardOK;
	}
//-------------------------------------------------------------------------
} //end class
