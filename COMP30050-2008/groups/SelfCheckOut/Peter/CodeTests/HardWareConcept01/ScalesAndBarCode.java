
public class ScalesAndBarCode extends Thread {

	public ScalesAndBarCode() {
		myScales1 = new ScalesClass01();
		myScales2 = new ScalesClass01();
		myBarCode = new BarCode01();
	}
	
	ScalesClass01 myScales1 = null;
	ScalesClass01 myScales2 = null;
	BarCode01 myBarCode = null;
	WeightAndCode myWeightAndCode = null;
	volatile boolean process = true;
	volatile int w1;
	volatile int w2;
	volatile int code;
	
	
	public void done() {
		myScales1.done();
		myScales2.done();
		myBarCode.done();
		process = false;
	}

	public WeightAndCode getWeightsAndCode() {
		return new WeightAndCode(myScales1.getWeight(),
								myScales2.getWeight(),
								myBarCode.getCode());
	}
	
	public void run() {
		myScales1.start();
		myScales2.start();
		myBarCode.start();
		while (process) {
			//setCode();
			try {
				sleep((int)(Math.random() * 1000));
			} catch (InterruptedException e) {}
		}
	}
}
