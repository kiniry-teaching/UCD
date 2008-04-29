package selfCheckOut.hardWareInterface;
import java.awt.image.BufferedImage;
import selfCheckOut.*;
import selfCheckOut.hardWareInterface.*;

/**
 * This thread class is used to decode barcodes from a passed image 
 * for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 * @version 31st March 2008.
 */


public class Decoder extends Thread {

	volatile boolean stopRequested = true;
	volatile boolean isStopped = true;
	volatile boolean workInProgress = false;
	volatile boolean outPutAvail = false;
	volatile Long timeStamp;
	
	private DecoderResult decoderResult = null;
	private int distributor = 0;
	private BufferedImage inImage = null;
	private Striper theStriper = null;
	private ImageMaker imageMaker = null;	
	private ImageTouchUp imTouchUp = null;
	// ------------------------------------------------------	
	public Decoder() { 
		super();
		stopRequested = false;
		isStopped = false;
	}
	// ------------------------------------------------------
	public synchronized void done() {
		stopRequested = true;
	}
	// ------------------------------------------------------
	private synchronized void setStopped() {
		isStopped = true;//have stopped running
	}
	// ------------------------------------------------------
	public synchronized boolean isStopped() {
		return isStopped;
	}
	// ------------------------------------------------------
	private synchronized boolean stopRequested() {
		return stopRequested;
	}
	// ------------------------------------------------------
	//pass the image to be decoded and mark the resulting barcode with 
	//a time stamp
	public synchronized boolean determineCode(BufferedImage inImage,
												Long timeStamp) {
		boolean accepted = false;
		if (!workInProgress  && !stopRequested && !outPutAvail) {
			accepted = true;
			this.inImage = inImage;
			this.timeStamp = timeStamp;
		}
		return accepted;
	}
	// ------------------------------------------------------
	//this returns the image used to decode
	private synchronized BufferedImage getProcessData() {
		BufferedImage tempImage = this.inImage; 
		if (tempImage != null){
			workInProgress = true;
			decoderResult = null;
			this.inImage = null; //stop us repeatadly getting same image
		}
		return tempImage;
	}
	// ------------------------------------------------------
	private synchronized void clearWorkInProgress() {
		workInProgress = false; //can now accept new data
	}
	// ------------------------------------------------------
	private synchronized void setResult(BufferedImage greyImage,	
										BufferedImage binImage,
										BarCode barNums) {
		decoderResult = 
			new DecoderResult(greyImage, binImage, barNums);
		outPutAvail = true;
		workInProgress = false; //can now accept new data
		
		System.out.println("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%");
		System.out.println(barNums);
		System.out.println("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%");
		
	}
	// ------------------------------------------------------
	public synchronized DecoderResult getResult() {
		DecoderResult tempOut;
		if (outPutAvail && !stopRequested) {
			tempOut = decoderResult;
			outPutAvail = false;//we have read the data
		} else {
			tempOut = null;
		}
		return tempOut;
	}
	// ------------------------------------------------------
	public void run() {
		BufferedImage processData;
		long startTime;
		long finishTime;
		int imageToUse = -1; //the type of image to use
		imageMaker = new ImageMaker(null);
		while (!stopRequested()) {
			switch (distributor) {
			case 0:
				startTime = System.currentTimeMillis();
				//System.out.println("distributor = " + distributor);
				processData = getProcessData();
				if (processData != null) {
					imageMaker.makeImages(processData);
				} else {
					clearWorkInProgress();
					distributor = -1; //this way after increment = 0, we keep repeating until we have got data
				}
				finishTime = System.currentTimeMillis();
				break;
			case 1:
				startTime = System.currentTimeMillis();
				imageToUse++;
				if (imageToUse == 8) 
					imageToUse = 0;
				theStriper = new Striper(imageMaker, 7);
				finishTime = System.currentTimeMillis();
				break;
			case 2:
				startTime = System.currentTimeMillis();
				theStriper.makeStripes();
				int processDat = theStriper.getNumRuns();
				if (processDat <=0 ) {
					setResult(null,
							imageMaker.getBinaryImage((imageToUse)),
							null);
					distributor = -1;//this way after increment = 0,
				}
				finishTime = System.currentTimeMillis();
				break;
			case 3:
				startTime = System.currentTimeMillis();
				BarCode gotCode = getCode(theStriper);
				
				if (gotCode != null){
					BufferedImage useImage = imageMaker.getGreyImage(imageToUse);
					useImage = imTouchUp.touchUpImage(useImage);
					useImage = imTouchUp.textUpImage(useImage,
									"Binary ImageType = " + 
									HWIHelper.padIntToString(imageToUse,4) +
									", = [" + HWIconst.binaryType[imageToUse] + "]");
					setResult(useImage,
							imageMaker.getBinaryImage(imageToUse),
							gotCode);
				} else {
					setResult(null,
							imageMaker.getBinaryImage((imageToUse)),
							null);
				}
				
				finishTime = System.currentTimeMillis();
				distributor = -1; //this way after increment = 0
				break;
			}
			distributor++;
			try {
				sleep(30);
			} catch (InterruptedException e) {
				System.out.println("Decoder() exception = " + e.toString());
				e.printStackTrace();
			}
		}
		setStopped();//have stopped running
	}
	
	//-------------------------------------------------
	private double[] calcStats(int numStripes, BarCodeStripe[] theStripes) {
		double[] retInf = new double[2];
		double stdDev = 0;
		double meanLen = 0;
		double sigmaLength = 0;
		double sigmaLenSqrd = 0;
		for (int i = 0; i < numStripes; i++) {
			sigmaLength = sigmaLength + theStripes[i].getLength();
			sigmaLenSqrd = sigmaLenSqrd + 
			(theStripes[i].getLength() * theStripes[i].getLength());
		}
		if (numStripes >0) {
			meanLen = (double)(sigmaLength/numStripes);
			stdDev = Math.sqrt(((double)sigmaLenSqrd / numStripes) - (meanLen * meanLen));
			//System.out.println(sigmaLength + ", " + sigmaLenSqrd);
		}
		if (HWIconst.DE_BUG) {
			System.out.println("stdDev = " + stdDev + 
					", meanLen = " + meanLen + 
					", sigmaLength = " + sigmaLength + 
					", sigmaLenSqrd = " + sigmaLenSqrd);
			}
		retInf[0] = stdDev;
		retInf[1] = meanLen;
		return retInf;
	}
	//--------------------------------------------------
	private double[] calcRegression(int numStripes, BarCodeStripe[] theStripes) {
		double[] retInf = new double[3];
		double sigXY = 0;
		double sigXX = 0;
		double sigYY = 0;
		double sigX = 0;
		double sigY = 0;
		double theSlope;
		double theIntercept;
		for (int i = 0; i < numStripes; i++) {
			sigX = sigX + theStripes[i].getCentrePos();
			sigXX = sigXX + 
					(theStripes[i].getCentrePos() * theStripes[i].getCentrePos());
			sigXY = sigXY + 
					(theStripes[i].getCentrePos() * (double)theStripes[i].getLineNum());
			sigYY = sigYY + 
					(theStripes[i].getLineNum() * (double)theStripes[i].getLineNum());
			sigY = sigY + (double)theStripes[i].getLineNum();
		}
		double ssXY = sigXY - ((sigX * sigY)/(numStripes));
		double ssXX = sigXX - ((sigX * sigX)/(numStripes));
		double ssYY = sigYY - ((sigY * sigY)/(numStripes));
		theSlope = ssXY/ssYY;
		theIntercept = (sigX/numStripes) - (theSlope*sigY/numStripes);
		double ssResid = ssXX - (theSlope*ssXY);
		double sError = Math.sqrt(ssResid /(double)numStripes);
	
		if (HWIconst.DE_BUG) {
			System.out.println("slope = " + theSlope + 
					", intercept = " + theIntercept + 
					", ssResid = " + ssResid + 
					", sError = " + sError);
		}
		retInf[0] = theIntercept;
		retInf[1] = theSlope;
		retInf[2] = sError;
		return retInf;
	}
	//------------------------------------------------------------
	public BarCode getCode(Striper theStriper) {
		
		assert theStriper !=null;
		BarCodeStripe[] gotStripes = theStriper.getStripes();
		int countBarStrips = theStriper.getNumStripes();
		imTouchUp = new ImageTouchUp();
		int goodLines = 0;
		int noisyLines = 0;
		int badLines = 0;
		double intercept = 0d;
		double slope = 0d;

		TentativeNumbers tNums = new TentativeNumbers();
		double[] summaryStats = calcStats(countBarStrips, gotStripes);
		double stdDev = summaryStats[0];
		double meanLen = summaryStats[1];
		
		if (HWIconst.DE_BUG) {
			System.out.println("Number of barStripes = " + countBarStrips);
		}
		int posCtr = 0;
		while (posCtr < countBarStrips) {
			if (HWIconst.DE_BUG) {
				System.out.println("posCtr = " + posCtr);
			}
			int len = gotStripes[posCtr].getLength(); 
			if ((len >= meanLen + (stdDev*2.0d)) || (len <= meanLen - (stdDev*2.0d))) {
				//mark this as a black line
				imTouchUp.storeTouch(gotStripes[posCtr], 2);
				if ( HWIconst.DE_BUG_FILTERING)
					if (HWIconst.DE_BUG) {
						System.out.println("rejected due to length out of range: " + 
								len + ", " + meanLen);
					}
				gotStripes[posCtr] = gotStripes[countBarStrips-1]; //0 based
				gotStripes[countBarStrips-1] = null; //prevent mem leak
				countBarStrips--;
				posCtr--;
			}
			posCtr++;
		}
		
		if (countBarStrips >5) {
			double[] regParams = calcRegression(countBarStrips, gotStripes); 
			intercept = regParams[0];
			slope =  regParams[1];
			imTouchUp.storeRegressionLine(intercept, slope);
			double sError = regParams[2];
			posCtr = 0;
			while (posCtr < countBarStrips) {
				double centre = gotStripes[posCtr].getCentrePos(); 
				double predY = intercept + slope*(double)gotStripes[posCtr].getLineNum(); 
				double resid = Math.abs(predY - centre);
				if (resid > sError*2.5) {
					// this is an orange line
					imTouchUp.storeTouch(gotStripes[posCtr], 4);
					if ( HWIconst.DE_BUG_FILTERING) 
						if (HWIconst.DE_BUG) {
							System.out.println("remove due to off regression line " +
									resid + ", " );
						}
					gotStripes[posCtr] = gotStripes[countBarStrips-1]; //0 based
					gotStripes[countBarStrips-1] = null; //prevent mem leak
					countBarStrips--;
					posCtr--;
				}
				posCtr++;
			}
		} //end if countBarStrips > 5
		if (HWIconst.DE_BUG) {
			System.out.println("Number of barStripes = " + countBarStrips +
					", Mean length = " + meanLen +
					", Standard dev = " + stdDev);
}
		for (int i = 0; i < countBarStrips; i++) {
			BarNums barNums = null;//want to be able to return null
			barNums = gotStripes[i].decodeStripe();//scanLine);
			if ((barNums != null) && barNums.numsHasEntry()) {	
				// add the discovered digits to possibles
				tNums.addToTentative(barNums);
				if (barNums.isValid(true)) {
					if (HWIconst.DE_BUG)
						System.out.println("Valid = " + barNums.numsToString());
					goodLines++;
					// 1 = this is a good line
					imTouchUp.storeTouch(gotStripes[i], 1);
				} else {
					if (HWIconst.DE_BUG)
						System.out.println("NOT! Valid = " + barNums.numsToString());
					if (barNums.hasDigits() > 0) {
						noisyLines++;
						// 0 = this is a noisy line
						imTouchUp.storeTouch(gotStripes[i], 0);
					}
				}
				// show the information that has been recognized along the scanline:
				if (HWIconst.DE_BUG) 
					System.out.println("ScanScope[i] " + i + 
							", result: " + barNums.numsToString() +
							". Prob: " + barNums.getProbability());
			} else {
				// 0 = this is a noisy line
				imTouchUp.storeTouch(gotStripes[i], 3);
				badLines++;
			}
		}

		if (HWIconst.DE_BUG) {
			System.out.println();
			System.out.println("detected digits:");
			System.out.println("# of their occurence:");
		}
		// get the most likely barcode:
		if (tNums.hasTents()) {
			tNums.showTentative();
		}
		if (HWIconst.DE_BUG) {
			System.out.println("goodLines = " + goodLines + 
					", noisyLines = " + noisyLines 
					+ ", badLines = " + badLines +
					", countBarStrips = " + countBarStrips);
		}
		//System.out.println("most probable Barcode = " + assembleBarcode());
		return tNums.assembleBarCode(timeStamp);
		//return assembleBarCode();
	}
	//-----------------------------------------------
}//end class
