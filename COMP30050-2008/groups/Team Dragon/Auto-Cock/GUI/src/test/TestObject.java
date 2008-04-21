/**
 * @author Lar
 * This tests how the nxt brick deals with referenced objects from other classes
 * 
 */
package test;

import lejos.nxt.LCD;

public class TestObject {

	private static int number;
	
	public TestObject(int number){
		TestObject.number = number;
	}
	
	public void print(){
		LCD.drawInt(TestObject.number, 0, 0);
	}
	
	public static void main(String[] args){}
}
