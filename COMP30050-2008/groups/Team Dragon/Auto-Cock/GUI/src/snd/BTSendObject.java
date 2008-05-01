/**
 * @author Lar
 * This class allows the GUI to create and call a basic bluetooth file exchange client.
 */
package snd;

//Import the required libraries
import lejos.pc.comm.*;

import java.io.*;

/**
 * Set up the class and create the required variables.
 * @author Lar
 *
 */
public class BTSendObject {

	private NXTInfo[] nxtInfo;
	private NXTComm nxtComm;
	private final String name = "NXT";
	private final String number = "001653012225";
	private boolean opened;
	private InputStream is;
	private OutputStream os;
	private DataOutputStream dos;
	private DataInputStream dis;
	private int resend=0;


	/**
	 * @author Lar
	 * @return a new BTSendObject
	 * @param void
	 *
	 */
	public BTSendObject(){
		nxtComm = NXTCommFactory.createNXTComm(NXTCommFactory.BLUETOOTH);
		nxtInfo = new NXTInfo[1];
		nxtInfo[0] = new NXTInfo(name, number);
		opened = false;
	}

	/**
	 * @author Lar
	 * @param whatAlexSends
	 * @return void
	 * This is the public method for starting the bluetooth file exchange. It can be called from any class that imports this class
	 */
	public void startClient(int[] whatAlexSends){
		start(whatAlexSends);
	}

	/**
	 * @author Lar
	 * @param void
	 * @return void
	 * This is the public method for stopping the bluetooth file exchange service.
	 */
	public void stopClient(){
		stop();
	}

	/**
	 * @author Lar
	 * @param whatAlexSends
	 * @return void
	 * This method is the private method for starting the bluetooth server. It takes in the order "int[] what AlexSends"
	 * it then opens the connection to the brick from a predefined name and uuid. Transfer is then called.
	 */
	private void start(int[] whatAlexSends){

		System.out.println("Connecting to " + nxtInfo[0].btResourceString);

		try {
			opened = nxtComm.open(nxtInfo[0]); 
		} catch (NXTCommException e) {
			System.out.println("Exception from open");
			e.printStackTrace();
		}

		if (!opened) {
			System.out.println("Failed to open " + nxtInfo[0].name);
			System.exit(1);
		}

		System.out.println("Connected to " + nxtInfo[0].btResourceString);

		transfer(whatAlexSends);

	}

	/**
	 * @author Lar
	 * @param void
	 * @return void
	 * Private method to stop the server. It closes all communications
	 */
	private void stop(){
		try {
			dis.close();
			dos.close();
			nxtComm.close();
		} catch (IOException ioe) {
			System.out.println("IOException closing connection:");
			System.out.println(ioe.getMessage());
		}
	}


	/**
	 * @author Lar
	 * @param p the order that we send
	 * @return void
	 * This method sends the order and waits to receive each individual int back. if the full order is not returned there is a re-attempt. 
	 * If there has been three attempts the transfer will be failed and the user will be asked to check their connection.
	 */
	private void transfer(int[] p){
		is = nxtComm.getInputStream();
		os = nxtComm.getOutputStream();

		dos = new DataOutputStream(os);
		dis = new DataInputStream(is);

		int[] alex = new int[7];

		for(int i=0;i<p.length;i++) {
			try {
				System.out.println("Sending " + p[i]);
				dos.writeInt(p[i]);
				dos.flush();			

			} catch (IOException ioe) {
				System.out.println("IO Exception writing bytes:");
				System.out.println(ioe.getMessage());
				break;
			}

			try {
				alex[i] = dis.readInt();
				System.out.println("Received " + dis.readInt());			
			} catch (IOException ioe) {
				System.out.println("IO Exception reading bytes:");
				System.out.println(ioe.getMessage());
				break;
			}
			resend++;
		}//for

		if(resend !=3){
			if(!compare(p,alex)){
				resend++;
				transfer(p);
			}
			else
				resend=0;
		}
		else
			System.out.println("Please Check your bluetooth connection");
	}

	/**
	 * @author Lar
	 * @param a the original order
	 * @param b the returned order
	 * @return boolean
	 * This method compares the order that was sent and the order that was received. This is to make sure the entire order reached the brick.
	 */
	private boolean compare(int[] a, int[] b){
		for(int i = 0; i< a.length; i++){
			if(a[i] != b[i]){
				return false;
			}
		}
		return true;
	}

}

