package selfCheckOut.hardWareInterface;

/**
 * This class is used to generate a run length code for the pixels 
 * in a scan line, this is an array of widths of groups of pixesl and
 * their colours.
 * <p>
 * 
 * @author Peter Gibney
 * @version 18th April 2008.
 */


public class Runner {
	private int[][] theRun = null;
	private int len = 0;
	private int lineNo;
	public Runner(int[] trace, int lineNo) {
		assert trace !=null;
		assert trace.length >0;
		assert lineNo >= 0;
		assert lineNo < 480;
		this.lineNo = lineNo;
		int[][] tempBars = new int[trace.length][2];
		int barCounter = 0;
		int barValue = trace[0];
		int pixelInBar = 1;
		for (int i = 1; i < trace.length; i++) {
			if ((trace[i] == barValue) && (i < trace.length - 1)) {
				pixelInBar++;
			} else {
				// create new field entry:
				tempBars[barCounter][0] = barValue;//black or white
				tempBars[barCounter][1] = pixelInBar;//number of pixels in the bar
				barValue = trace[i];
				// pixelInBar = 0;
				pixelInBar = 1;
				barCounter++;
			}
		}
		theRun = new int[barCounter][2];
		for (int i = 0; i < barCounter; i++) {
			theRun[i][0] = tempBars[i][0];
			theRun[i][1] = tempBars[i][1];
		}
		len = barCounter;
	}
	//--------------------------------------------------
	public int getLength() {
		return len;
	}
	//--------------------------------------------------
	public int getLineNo() {
		return lineNo;
	}
	//--------------------------------------------------
	public int[][] getRunner() {
		return theRun;
	}
	//--------------------------------------
} //end class
