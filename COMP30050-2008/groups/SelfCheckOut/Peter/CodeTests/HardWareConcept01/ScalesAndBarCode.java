
public class ScalesAndBarCode extends Thread {

	ScalesClass01 myScales1 = null;
	ScalesClass01 myScales2 = null;
	BarCode01 myBarCode = null;
	WeightAndCode myWeightAndCode = null;
	volatile boolean stopRequested = true;
	volatile boolean isStopped = true;
	volatile int w1;
	volatile int w2;
	volatile int code;
	// ------------------------------------------------------	
	public ScalesAndBarCode() {
		myScales1 = new ScalesClass01();
		myScales2 = new ScalesClass01();
		myBarCode = new BarCode01();
		stopRequested = false;
		isStopped = false;
	}
	// ------------------------------------------------------	
	public void done() {
		//stop sub threads
		synchronized (this) {
			stopRequested = true;
			myBarCode.done();
			myScales1.done();
			myScales2.done();
		} //end sync
		
		while (!myBarCode.isStopped() || 
				!myScales1.isStopped() || 
				!myScales1.isStopped()) {
			if (HWIconst.DE_BUG_THREAD_SHUT_DOWN) {
				System.out.println("In: ScalesAndBarCode.done(), waiting:");
				System.out.println("          myBarCode.isStopped()= " + 
						myBarCode.isStopped());
				System.out.println("          myScales1.isStopped()= " + 
						myScales1.isStopped());
				System.out.println("          myScales2.isStopped()= " + 
						myScales2.isStopped());
			}
			try {
				Thread.sleep(55);
			} catch (Exception ex) {
				System.out.println("ScalesAndBarCode() exception = " + ex.toString());
				ex.printStackTrace();
			}
		}
	}
	// ------------------------------------------------------
	private synchronized void setStopped() {
		isStopped = true;//have stopped running
	}
	// ------------------------------------------------------
	public synchronized boolean isStopped() {
		return isStopped && 
		myBarCode.isStopped() &&
		myScales1.isStopped() &&
		myScales2.isStopped();
	}
	// ------------------------------------------------------	
	public synchronized WeightAndCode getWeightsAndCode() {
		if (stopRequested) {
			return null;
		} else {
			return new WeightAndCode(myScales1.getWeight(),
								myScales2.getWeight(),
								myBarCode.getCode());
		}
	}
	// ------------------------------------------------------
	private synchronized boolean stopRequested() {
		return stopRequested;
	}
	// ------------------------------------------------------
	public void run() {
		myScales1.start();
		myScales2.start();
		myBarCode.start();
		while (!stopRequested()) {
			//setCode();
			try {
				sleep(100);
				//sleep((int)(Math.random() * 10000));
			} catch (InterruptedException e) {
				System.out.println("InterruptedException: ScalesAndBarCode()");
				e.printStackTrace();
			}
		}
		setStopped();
	}
}
