package snd;

import lejos.pc.comm.*;

import java.io.*;

public class BTSendObject {

	private NXTInfo[] nxtInfo;
	private NXTComm nxtComm;
	private final String name = "NXT";
	private final String number = "001653012225";
	private int[] order;
	private boolean opened;
	private InputStream is;
	private OutputStream os;
	private DataOutputStream dos;
	private DataInputStream dis;
	

	public BTSendObject(){
		nxtComm = NXTCommFactory.createNXTComm(NXTCommFactory.BLUETOOTH);
		nxtInfo = new NXTInfo[1];
		nxtInfo[0] = new NXTInfo(name, number);
		opened = false;
		order = new int[7];
	}

	public void startClient(){
		start();
	}

	public void stopClient(){
		stop();
	}

	private void start(){

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

		transfer();

	}

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


	private void transfer(){
		is = nxtComm.getInputStream();
		os = nxtComm.getOutputStream();

		dos = new DataOutputStream(os);
		dis = new DataInputStream(is);

		for(int i=0;i<7;i++) {
			try {
				System.out.println("Sending " + i);
				dos.writeInt(i);
				dos.flush();			

			} catch (IOException ioe) {
				System.out.println("IO Exception writing bytes:");
				System.out.println(ioe.getMessage());
				break;
			}

			try {
				System.out.println("Received " + dis.readInt());
			} catch (IOException ioe) {
				System.out.println("IO Exception reading bytes:");
				System.out.println(ioe.getMessage());
				break;
			}
		}

	}

}

