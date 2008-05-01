/**
 * @author Lar
 * @deprecated
 * This is the bluetooth file exchange before made into objects
 */
package rcv;
import lejos.nxt.*;
import lejos.nxt.comm.*;
import java.io.*;

public class BTReceive {

	public BTReceive(){

	}
	public static void main(String [] args)  throws Exception 
	{
		final String autocock = "Autocock";
		final String mouth1 = "..Mouth Watering";
		final String mouth2 = "cumming soon" ;
		final String order = "Receiving order";
		final String closing = "Closing...";

		while (true)
		{
			LCD.drawString(autocock,0,0);
			LCD.drawString(mouth1,0,5);
			LCD.refresh();

			BTConnection btc = Bluetooth.waitForConnection();

			LCD.clear();
			LCD.drawString(order,0,0);
			LCD.drawString(mouth2,0,5);
			LCD.refresh();	

			DataInputStream dis = btc.openDataInputStream();
			DataOutputStream dos = btc.openDataOutputStream();

			for(int i=0;i<100;i++) {
				int n = dis.readInt();
				LCD.drawInt(n,7,0,1);
				LCD.refresh();
				dos.writeInt(-n);
				dos.flush();
			}

			dis.close();
			dos.close();
			Thread.sleep(100); // wait for data to drain
			LCD.clear();
			LCD.drawString(closing,0,0);
			LCD.refresh();
			btc.close();
			LCD.clear();
		}
	}
}

