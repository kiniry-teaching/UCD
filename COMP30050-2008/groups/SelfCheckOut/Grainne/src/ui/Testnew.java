package ui;

public class Testnew {
	
	public static void main(String[] args)
	{
		Test t = new Test();
		t.initGUI();
		
		System.out.print("hello");
		while (true) {
			System.out.print("in while loop");
	         try { // Poll every ~10 ms
	            Thread.sleep(10);
	         }
	         catch (InterruptedException e) {}
	         
	         t.appendToChatBox("INCOMING: " + "\n");
	      }
	}

}
