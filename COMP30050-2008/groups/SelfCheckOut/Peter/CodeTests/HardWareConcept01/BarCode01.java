import java.util.Random;

public class BarCode01 extends Thread {

	volatile boolean stopRequested = true;
	volatile boolean isStopped = true;
	volatile int code;
	Random rand = null;
	
	public BarCode01() { 
		super();
		stopRequested = false;
		isStopped = false;
		rand = new Random();
	}
	// ------------------------------------------------------
	public int getCode() {
		synchronized (this) {
			return code;
		}
	}
	// ------------------------------------------------------
	private void setCode() {
		synchronized (this) {
			code = rand.nextInt(1000);
		}
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
	public void run() {
		while (!stopRequested()) {
			setCode();
			try {
				sleep(100);
				//sleep((int)(Math.random() * 10000));
			} catch (InterruptedException e) {
					System.out.println("BarCode01() interrupted exception");
					e.printStackTrace();
			}
		}
		setStopped();//have stopped running
	}
}
