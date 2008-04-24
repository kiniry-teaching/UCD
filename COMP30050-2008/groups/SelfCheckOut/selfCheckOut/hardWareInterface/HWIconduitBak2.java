package selfCheckOut.hardWareInterface;
/**
 * This  class is used to communicate the Barcodes and weights
 *  to the main loop for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 * @version 30th March 2008.
 */

//import Striper;
import selfCheckOut.BarCode;
import selfCheckOut.SelfCheckOut;
import selfCheckOut.Weight;
import selfCheckOut.hardWareInterface.HardWareResult;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Scanner;

import java.util.Random;
import java.util.concurrent.*;

public class HWIconduit extends Thread {
	
	volatile boolean stopRequested = true;
	volatile boolean isStopped = true;
	volatile boolean gather = false;
	
	private BlockingQueue<HardWareResult> queue =
		new LinkedBlockingQueue<HardWareResult>();

	
	// ------------------------------------------------------	
	public HWIconduit() { 
		super();
		stopRequested = false;
	}
	// ------------------------------------------------------
	public HardWareResult getHardWareResult() {
		HardWareResult tempHWR = null;
		//System.out.println("HWIconduit point 1");
		try {
			//System.out.println("HWIconduit point 2");
			tempHWR = queue.poll(5L, TimeUnit.MILLISECONDS);
			//System.out.println("HWIconduit point 3");
		} catch (InterruptedException e) {
			System.out.println("HWIconduit() exception = " + e.toString());
			//e.printStackTrace();
		}
		//System.out.println("HWIconduit point 4");
		return tempHWR;
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
	public synchronized void gather(boolean gather) {
		this.gather= gather;
	}
	// ------------------------------------------------------
	private synchronized boolean doGather() {
		return this.gather;
	}
	// ------------------------------------------------------
	
	public void run() {
		String inFile = "shopping.txt";
		Scanner in = null;
		try {
			FileReader reader = new FileReader(inFile);
			in = new Scanner(reader);
		} catch (IOException exception){
			System.out.println("Error with file");
		}
		
		BarCode[] barCodeList = null;
		Random myRandom = new Random();
		int posMarker = 0;
		HardWareResult hwr = null;
		Weight wgt1 = null;
		Weight wgt2 = null;
		long fileInput = 0;
		while (!stopRequested() && in.hasNextLong()) {
			if (doGather()) {
				//long fileInput = in.nextLong();
				System.out.println(fileInput);
				switch (posMarker) {
					case 0:
						System.out.println("At stage: " + posMarker);
						fileInput = in.nextLong();
						wgt1 = new Weight((int)fileInput);
						hwr = new HardWareResult(barCodeList, wgt1, wgt2);
						queue.add(hwr);
						posMarker++;
						break;
					case 1:
						System.out.println("At stage: " + posMarker);
						fileInput = in.nextLong();
						double prob1 = myRandom.nextDouble();
						long bar1 = fileInput;
						long bar2 = in.nextLong();
						int checkDigit = 0;
						//System.out.println("At stage: " + posMarker + "b1 = " + bar1 + "b2 = " + bar2);
						if (bar2 == 0l) {
							//one barcode
							barCodeList = new BarCode[1];
							String barStr = "" + bar1;
							checkDigit = BarCode.getPotentialCheckDigit(barStr);
							bar1  = (bar1 * 10) + checkDigit;
							barCodeList[0] = new BarCode(bar1, prob1);
						} else {
							// two barcodes
							barCodeList = new BarCode[2];
							String barStr = "" + bar1;
							checkDigit = BarCode.getPotentialCheckDigit(barStr);
							bar1  = (bar1 * 10) + checkDigit;
							barCodeList[0] = new BarCode(bar1, prob1);
							
							double prob2 = prob1/1.8d;
							barStr = "" + bar2;
							checkDigit = BarCode.getPotentialCheckDigit(barStr);
							bar2  = (bar2 * 10) + checkDigit;
							barCodeList[1] = new BarCode(bar2, prob2);
						}
						hwr = new HardWareResult(barCodeList, wgt1, wgt2);
						queue.add(hwr);
						posMarker++;
						break;
					case 2:
						fileInput = in.nextLong();
						System.out.println("At stage: " + posMarker);
						wgt2 = new Weight((int)fileInput);
						hwr = new HardWareResult(barCodeList, wgt1, wgt2);
						queue.add(hwr);
						posMarker++;
						break;
					case 3:
						System.out.println("At stage: " + posMarker);
						hwr = new HardWareResult(barCodeList, wgt1, wgt2);
						queue.add(hwr);
						wgt1 = null;
						wgt2 = null;
						barCodeList = null;
						posMarker = 0;
						break;
				}
			}
			try {
				sleep(1100 + myRandom.nextInt(500));
			} catch (InterruptedException e) {
				System.out.println("HWIconduit() exception = " + e.toString());
				e.printStackTrace();
			}
		}
		setStopped();//have stopped running
	}

}
