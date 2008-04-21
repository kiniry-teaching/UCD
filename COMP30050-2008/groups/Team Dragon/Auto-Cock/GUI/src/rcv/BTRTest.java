package rcv;

public class BTRTest {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		BTRObject bt = new BTRObject();
		while(true){
			bt.startServer();
			bt.stopServer();
		}
	}
}
