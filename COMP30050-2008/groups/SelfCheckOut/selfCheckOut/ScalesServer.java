package selfCheckOut;
import java.io.*;
import selfCheckOut.hardWareInterface.HardWareResult;
import selfCheckOut.netWork.ResultPumper;
import com.phidgets.*; 
import com.phidgets.event.*; 

/**
 * This class is used to get the weights from the scales throught the Phidgets,
 * and to transmit them to the ProcessHardWare, in order for this to run you
 * will need the Phidget .jar file in the classpath.
 * <p>
 * Command line to run: 
 * 
 * java -classpath .;Phidget21.jar -ea selfCheckOut.ScalesServer
 * <p>
 * 
 * @author Peter Gibney
 * @version 15th April 2008.
 */

public class ScalesServer {

//http://www.javacoffeebreak.com/java109/java109.html
//http://java.sun.com/docs/books/tutorial/networking/sockets/clientServer.html
//http://docs.rinet.ru/JaTricks/ch34.htm#JavaTCPIPSockets


	
	private ResultPumper rp = null;
	private InterfaceKitPhidget myInterface; 
	
	public ScalesServer() { 
		try{ 
			myInterface = new InterfaceKitPhidget(); 
			myInterface.addAttachListener(
					new AttachListener() 
					{public void attached(AttachEvent ae) 
						{ System.out.println("attachment of " + ae);}}); 
		} catch(PhidgetException e){ 
			System.out.println("Phidget Exception launched by TemperatureSensorPhidget() number " + e.getErrorNumber()); 
			System.out.println(e.getDescription()); 
		} 
		try{ 
			myInterface.open(68699); 
			System.out.println("Waiting for Attachment "); 
			myInterface.waitForAttachment();
			System.out.println("Attached?  " + myInterface.isAttached()); 
		} catch(PhidgetException e){ 
			System.out.println("Phidget Exception launched by open(68699) number " + e.getErrorNumber()); 
			System.out.println(e.getDescription()); 
		} 
		try{ 
			System.out.print("Number of sensors = : "); 
			System.out.println(this.myInterface.getSensorCount()); 
		} catch(PhidgetException e){ 
			System.out.println("Phidget Exception launched by getSensorCount() number " + e.getErrorNumber()); 
			System.out.println(e.getDescription()); 
		} 
		try{ 
			System.out.print("Number of sensors = : "); 
			System.out.println(this.myInterface.getSensorCount()); 
		} catch(PhidgetException e){ 
			System.out.println("Phidget Exception launched by getSensorCount() number " + e.getErrorNumber()); 
			System.out.println(e.getDescription()); 
		} 
		rp = new ResultPumper(4444);
	}
	//-----------------------------------------------------------
	public void begin() {
		rp.start();
		int prevVal1 = 0;
		int prevVal2 = 0;
		while (true) {
			int valScales1 = 0;
			int valScales2 = 0;
			try{ 
				valScales1 = myInterface.getSensorRawValue(0);//2
				valScales2 = myInterface.getSensorRawValue(7);//5
				System.out.println("Sensor 0 = " + valScales1 +
					",  Sensor 7 = " + valScales2);
			} catch (PhidgetException e){
				System.out.println("Phidget Exception launched by TemperatureSensorPhidget() number " + e.getErrorNumber()); 
				System.out.println(e.getDescription()); 
			}
			boolean valsChanged = false;
			if (Math.abs(prevVal1 - valScales1 ) >=2) {
				valsChanged = true;
			}
			if (Math.abs(prevVal2 - valScales2 ) >=2) {
				valsChanged = true;
			}
			prevVal1 = valScales1;
			prevVal2 = valScales2;
			if (rp.accepted() && valsChanged) {
				HardWareResult hwr = new HardWareResult(null,
										new Weight(valScales1),
										new Weight(valScales2));
				rp.pumpResults(hwr);
			}
			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		} //end while loop
		
	}
	//-----------------------------------------------------------
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
	
	private static ScalesServer ss;
	public static void main(String[] args) throws IOException {
		ss= new ScalesServer();
		ss.begin();
	}
}

