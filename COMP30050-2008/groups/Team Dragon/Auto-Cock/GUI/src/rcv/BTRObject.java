/**
 * 
 * @author Lar
 * Class for bluetooth file exchange on the brick. Allows simple method calls to start/stop a server
 * 
 */

package rcv;
import lejos.nxt.*;
import lejos.nxt.comm.*;

import java.io.*;

/**
 * 
 * @author Lar
 * Setting up of variables
 */
public class BTRObject {

	DataInputStream dis;
	DataOutputStream dos;
	BTConnection btc;


	private int[] order; 
	final private String autocock = "Autocock";
	final private String mouth1 = "..Mouth Watering";
	final private String mouth2 = "cumming soon" ;
	final private String receiving = "taking it hard";
	final private String closing = "Pulling out";
	final private String received = "order received";
	final private String processing = "processing order";

	/**
	 * @author Lar
	 * @param void
	 * Creates a new Object to receive orders with space for an order with 7 ingredients
	 */
	public BTRObject(){
		order = new int[7];
	}

	/**
	 * @author Lar
	 * @param void
	 * @return void
	 * A public method to start the server
	 */
	public void startServer(){
		try {
			start();
		} catch (IOException e) {

		}

	}

	/**
	 * @author Lar
	 * @param void
	 * @return void
	 * A public method to stop the server
	 */
	public void stopServer(){
		try {
			stop();
		} catch (InterruptedException e) {

		} catch (IOException e) {

		}
	}

	/**
	 * @author Lar
	 * @param i where in the order the drink is added
	 * @param drink the drink to be added
	 * This method allows drinks to be added to a particular object
	 */
	public void addDrink(int i, int drink){
		order[i] = drink;
	}

	/**
	 * @author Lar
	 * @param void
	 * @return int[] order
	 * This method returns the order contained within a particular BTRObject
	 */
	public int[] getOrder(){
		return order;
	}

	/**
	 * @deprecated
	 * Lejos cannot concatenate Strings so method body commented out
	 * Method was built for testing only so, no biggie.
	 */
	public void printOrder(){
		//String o = null;
		//for(int i = 0; i<order.length;i++){
		//o = o.concat(Integer.toString(i));
		//}
		//LCD.drawString(o,0,0);
	}

	/**
	 * @author Lar
	 * @param void
	 * @return void
	 * @throws IOException
	 * 
	 * This is a private method to start the bluetooth server
	 */
	private void start() throws IOException{
		LCD.drawString(autocock,0,0);
		LCD.drawString(mouth1,0,5);
		LCD.refresh();
		btc = Bluetooth.waitForConnection();
		try {
			listen();
		} catch (IOException e) {

		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			//e.printStackTrace(); We can't print stack traces in lejos
		}
	}

	/**
	 * @author Lar
	 * @throws InterruptedException
	 * @throws IOException
	 * 
	 * Private method to stop the server.
	 */
	private void stop() throws InterruptedException, IOException{
		dis.close();
		dos.close();
		Thread.sleep(100); // wait for data to drain
		LCD.clear();
		LCD.drawString(closing,0,0);
		LCD.refresh();
		btc.close();
		LCD.clear();
	}

	/**
	 * @author Lar
	 * @param void
	 * @return void
	 * @throws IOException
	 * @throws InterruptedException
	 * 
	 * This method takes in orders and adds them to the object's array. It then returns the int it takes in so the order can be checked at the sender's end.
	 */
	private void listen() throws IOException, InterruptedException{

		LCD.clear();
		LCD.drawString(receiving,0,0);
		LCD.drawString(mouth2,0,5);
		LCD.refresh();	

		dis = btc.openDataInputStream();
		dos = btc.openDataOutputStream();

		for(int i=0;i<7;i++) {
			int n = dis.readInt();
			if(n == 998 || n == 999){
				addDrink(i,n);
				LCD.drawInt(n,7,0,1);
				LCD.refresh();
				dos.writeInt(n);
				dos.flush();
				break;
			}

			else{
				addDrink(i,n);
				LCD.drawInt(n,7,0,1); 
				LCD.refresh();
				dos.writeInt(n);
				dos.flush();
			}
		}
		dos.flush();
	}

	/**
	 * @author Lar
	 * @param args
	 * 
	 * Every class on the Lejos brick requires a main method.
	 */
	public static void main(String []args){} 

}
