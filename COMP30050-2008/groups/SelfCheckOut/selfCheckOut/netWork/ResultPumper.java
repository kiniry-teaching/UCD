package selfCheckOut.netWork;

//import selfCheckOut.BarCode;
//import selfCheckOut.SelfCheckOut;
//import selfCheckOut.Weight;
//import selfCheckOut.hardWareInterface.HardWareResult;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.concurrent.*;
import java.net.*;
import selfCheckOut.hardWareInterface.HardWareResult;


//package selfCheckOut.hardWareInterface;
/**
 * This  class is used to communicate the Barcodes and weights
 *  to the network for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 * @version 21th April 2008.
 */

public class ResultPumper extends Thread {
volatile private boolean stopRequested = true;
volatile private boolean isStopped = true;
volatile private boolean accepted = false; //
private ServerSocket serverSocket = null;
private HardWareResult prevHWR = null;

private BlockingQueue<HardWareResult> queue =
	new LinkedBlockingQueue<HardWareResult>();
// ------------------------------------------------------	
public ResultPumper(int usePort) { 
	stopRequested = false;
	try {
		InetAddress localaddr = InetAddress.getLocalHost();
		System.out.println ("Local IP Address : " + localaddr );
		System.out.println ("Local hostname   : " + localaddr.getHostName());
	} catch (UnknownHostException e) {
		System.err.println ("Can't detect localhost : " + e);
		System.exit(1);
	}
	try {
		serverSocket = new ServerSocket(usePort);
	} catch (IOException e) {
		System.err.println("Could not listen on port: " + usePort);
		System.exit(1);
	}
}
// ------------------------------------------------------
/** Converts a byte_array of octets into a string */
public String byteToStr( byte[] byte_arr ) {
	StringBuffer internal_buffer = new StringBuffer();

	// Keep looping, and adding octets to the IP Address
	for (int index = 0; index < byte_arr.length -1; index++)
	{
		internal_buffer.append ( String.valueOf(byte_arr[index]) + ".");
	}
	
	// Add the final octet, but no trailing '.'
	internal_buffer.append ( String.valueOf (byte_arr.length) );
	return internal_buffer.toString();
}
// ------------------------------------------------------
public void pumpResults(HardWareResult hwr) {
	assert hwr != null;	
	if (hwr != null && accepted() && !hwr.sameValues(prevHWR)) {
		//here is where we put in queue
		prevHWR = hwr;
		queue.add(hwr);
		System.out.println("+ 2.queue.size() = " + queue.size() +
				", " + hwr.toString());
		//System.out.print("+");
	}
}
// ------------------------------------------------------
public HardWareResult getHardWareResult() {
	HardWareResult tempHWR = null;
	//System.out.println("HWIconduit point 1");
	try {
		tempHWR = queue.poll(5L, TimeUnit.MILLISECONDS);
	} catch (InterruptedException e) {
		System.out.println("HWIconduit() exception = " + e.toString());
		//e.printStackTrace();
	}
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
private synchronized void setAccepted(boolean state) {
	accepted = state;
}
// ------------------------------------------------------
public synchronized boolean accepted() {
	return accepted;
}
// ------------------------------------------------------

public void run() {
	Socket clientSocket = null;
	PrintWriter out = null;
	String outputLine;
	boolean localAccepted = false; 
	while (!stopRequested()) {
		if (!accepted()) {
			localAccepted = true; //assume we will make a connection
			try {
				serverSocket.setSoTimeout(200);
				clientSocket = serverSocket.accept();
			} catch (SocketTimeoutException e) {
				System.err.println("1: Accept failed. " + e);
				localAccepted = false; //did not make a connection
			} catch (IOException e) {
				System.err.println("2: Accept failed. " + e);
				System.exit(1);
			}
			if (localAccepted) {
				setAccepted(true);//made a connection
				System.err.println("Accepted ");
		        try {
					out = new 
						PrintWriter(clientSocket.getOutputStream(), true);
		        } catch (Exception e) {
		        	System.out.print("Error:  " + e);// + i);
		        }
			}
		} else {
			HardWareResult hwr = getHardWareResult();
			if (hwr != null) { 
				outputLine = hwr.exportHardWareResult();
				out.println(outputLine);
				out.println(outputLine);
				//out.println(outputLine);
			}
		}
		try {
			sleep(50);
		} catch (InterruptedException e) {
			System.out.println("ResultPumper exception = " + e.toString());
			e.printStackTrace();
		}
	}
	try {
		out.close();
		clientSocket.close();
		serverSocket.close();
	} catch (Exception e) {
		System.out.print("Error:  " + e);// + i);
	}
	setStopped();//have stopped running
} //end run()
} //end class



