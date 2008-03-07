
public class BarCode01 extends Thread {
	public BarCode01() { 
		super();
	}
	volatile int code;
	volatile boolean process = true;
	
	public int getCode() {
		synchronized (this) {
			return code;
		}
	}
 
	private void setCode() {
		synchronized (this) {
			code = (int)(Math.random() * 100);
		}
	}

	public void done() {
		process = false;
	}
	
	public void run() {
		while (process) {
			setCode();
			try {
				sleep((int)(Math.random() * 1000));
			} catch (InterruptedException e) {}
		}
	}
}
