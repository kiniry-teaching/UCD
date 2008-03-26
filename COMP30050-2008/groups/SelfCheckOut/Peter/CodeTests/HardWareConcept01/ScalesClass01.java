import java.util.Random;

public class ScalesClass01 extends Thread { 

	volatile int weight;
	volatile boolean stopRequested = true;
	volatile boolean isStopped = true;
	Random rand = null;
	// ------------------------------------------------------
	public ScalesClass01() { 
		super();
		rand = new Random();
		stopRequested = false;
		isStopped = false;
	}
	// ------------------------------------------------------
	public int getWeight() {
		synchronized (this) {
			return weight;
		} //end synchronized
	}
	// ------------------------------------------------------
	private void setWeight() {
		synchronized (this) {
			weight = rand.nextInt(1000);
		}
	}
	// ------------------------------------------------------
	public synchronized void done() {
		stopRequested = true;
	}
	// ------------------------------------------------------
	private synchronized boolean stopRequested() {
		return stopRequested;
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
	public void run() {
		while (!stopRequested()) {
			setWeight();
			try {
				sleep(10);
			} catch (InterruptedException e) {
				System.out.println("ScalesClass01() InterruptedException ");
				e.printStackTrace();
			}
		}
		setStopped();//have stopped running
	}
}
