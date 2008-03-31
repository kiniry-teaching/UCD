package selfCheckOut.hardWareInterface;
/**
 * This  class is used to communicate the Barcodes and weights
 *  to the main loop for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 * @version 30th March 2008.
 */

import selfCheckOut.SelfCheckOut;
import selfCheckOut.Weight;
import selfCheckOut.BarCode;
import selfCheckOut.hardWareInterface.HardWareResult;
import java.util.Random;
import java.util.concurrent.*;
import java.util.concurrent.TimeUnit;

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
	private void wasteTime() {
		long currTime = System.currentTimeMillis();
		boolean waitForChange = true;
		while (waitForChange) {
			long newTime = System.currentTimeMillis();
			waitForChange = (newTime == currTime);
		}
	}
	// ------------------------------------------------------
	
	public void run() {
		Random myRandom = new Random();
		myRandom.nextInt(5000);
		
		int initWgt = myRandom.nextInt(5000) + 1000;
		int w1 = initWgt;
		int w2 = 0;
		while (!stopRequested()) {
			if (doGather()) {
				int numBars = myRandom.nextInt(5) + 1;
				int deltaWt = myRandom.nextInt(200) + 25;
				if (w1 == 0) {
					initWgt = myRandom.nextInt(5000) + 1000;
					w1 = initWgt;
					w2 = 0;
					numBars = 0;
				} else {
					w1 = w1 - deltaWt;
					w2 = w2 + deltaWt;
					if (w1 <=0) {
						w1 = 0;
						w2 = initWgt;
					}
				}
				Weight wgt1 = new Weight(w1);
				BarCode[] barCodeList = new BarCode[numBars];
				for (int i= 0; i < numBars; i++) {
					wasteTime();
					long barLong = 1000007000001l + 
									(long)(myRandom.nextInt(80000000) +
									(long)(myRandom.nextInt(80000000)));
					String barStr = "" + barLong;
					barCodeList[i] = new BarCode(barStr);
				}
				wasteTime();
				Weight wgt2 = new Weight(w2);
				HardWareResult hwr = new HardWareResult(barCodeList, wgt1, wgt2);
				queue.add(hwr);
			}
			try {
				sleep(1900);
				//sleep((int)(Math.random() * 10000));
			} catch (InterruptedException e) {
				System.out.println("HWIconduit() exception = " + e.toString());
				e.printStackTrace();
			}
		}
		setStopped();//have stopped running
	}

}
