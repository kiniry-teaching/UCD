package selfCheckOut.netWork;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Scanner;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import selfCheckOut.hardWareInterface.HardWareResult;
import selfCheckOut.hardWareInterface.HWIconst;
//import selfCheckOut.Weight;

/**
 * This thread class is used to recieve HardWareResult objects that
 * have been sent across the network for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 */



public class PumpReciever extends Thread {

	private volatile boolean stopRequested = true;
	private volatile boolean isStopped = true;
	//private volatile boolean outPutAvail = false;
	//private volatile Weight[] outPutWeights = null;
	private BlockingQueue<HardWareResult> queue =
		new LinkedBlockingQueue<HardWareResult>();
	private final int usePort;
	private final String AddressIP;
	private volatile boolean gather = false;
	// ------------------------------------------------------	
	public PumpReciever(String AddressIP, int usePort) {
		stopRequested = false;
		isStopped = false;
		//outPutAvail = false;
		//outPutWeights = new Weight[2];
		this.AddressIP = AddressIP;
		this.usePort = usePort;
	}
	// ------------------------------------------------------	
	public void done() {
		//stop sub threads
		synchronized (this) {
			stopRequested = true;
		} //end sync
		
		while (!isStopped()) {
			if (HWIconst.DE_BUG_THREAD_SHUT_DOWN) {
				System.out.println("In: ScalesAndBarCode.done(), waiting:");
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
		return isStopped;
	}
	// ------------------------------------------------------
	public HardWareResult getHardWareResult() {
		HardWareResult tempHWR = null;
		//System.out.println("HWIconduit point 1");
		if (!stopRequested() && !isStopped()){
			try {
				tempHWR = queue.poll(5L, TimeUnit.MILLISECONDS);
			} catch (InterruptedException e) {
				System.out.println("HWIconduit() exception = " + e.toString());
				//e.printStackTrace();
			}
		}
		return tempHWR;
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
		HardWareResult prevHWR = null;
		Socket scalesSocket = null;
		PrintWriter out = null;
		BufferedReader in = null;
		//String addressStr = "127.0.0.1";
		String addressStr = AddressIP;
		boolean connected = false; //

		while (!connected && !stopRequested()) {
			connected = true; //assume we will make a connection
			try {
			//192.168.13.1
			//192.168.184.1
			//137.43.177.213
			scalesSocket = new Socket(addressStr, this.usePort);
			} catch (UnknownHostException e) {
				System.err.println("Don't know about host: " + addressStr);
				connected = false;
			} catch (IOException e) {
				connected = false;
				System.err.println("Couldn't get I/O for the connection to: " 
						+ addressStr + ", stopReq = " + stopRequested());
			}catch (Exception e) {
				connected = false;
				System.err.println("Exception :" +  e);
			}
			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
				System.err.println("Exception ScalesClient..");
				e.printStackTrace();
			}
		}
		
		Scanner lineScanner = null;
		if (connected) {
			try {
				out = new PrintWriter(scalesSocket.getOutputStream(), true);
				in = new BufferedReader(new InputStreamReader(scalesSocket.getInputStream()));
			} catch (Exception e) {
				System.out.print("Error:  " + e);// + i);
			}
			lineScanner = new Scanner(in);
		}
		
		while (!stopRequested() && connected) {
			if (lineScanner.hasNextLine()) {
				String lineStr = lineScanner.nextLine();
				Scanner inScan = new Scanner(lineStr);
				HardWareResult hwr1 = HardWareResult.importHardWareResult(inScan);
				if (hwr1 == null){
					System.out.println("Server Error! : " + lineStr);
				} else {
					//System.out.println("Server: " + hwr1);//fromServer);
					if (!hwr1.sameValues(prevHWR) && doGather()) {
						queue.add(hwr1);
						System.out.println("queue.size() = " + queue.size());
						prevHWR = hwr1;
					} else {
						//System.out.print("*");
					}
				}
			}
			try {
				sleep(50);
			} catch (InterruptedException e) {
				System.out.println("InterruptedException: ScalesClient()");
				e.printStackTrace();
			}
		}
		if (connected) {
			try {
				out.close();
			} catch (Exception e) {
				System.out.println("Error:  ScalesClient() out.close() " + e);// + i);
			}

			try {
				in.close();
			} catch (Exception e) {
				System.out.println("Error:  ScalesClient() in.close() " + e);// + i);
			}
			
			try {	
				scalesSocket.close();
			} catch (Exception e) {
				System.out.println("Error:  ScalesClient() scalesSocket.close() " + e);// + i);
			}
		}
		setStopped();
	}
}

