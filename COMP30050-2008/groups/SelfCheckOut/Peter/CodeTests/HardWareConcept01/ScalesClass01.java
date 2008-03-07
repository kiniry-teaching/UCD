
public class ScalesClass01 extends Thread { 

	public ScalesClass01() { 
		super();
	}
	volatile int weight;
	volatile boolean process = true;
	
	public int getWeight() {
		synchronized (this) {
			return weight;
		}
	}
 
	private void setWeight() {
		synchronized (this) {
			weight = (int)(Math.random() * 100);
		}
	}

	public void done() {
		process = false;
	}
	
	public void run() {
		while (process) {
			setWeight();
			try {
				sleep((int)(Math.random() * 1000));
			} catch (InterruptedException e) {}
		}
	}
}
