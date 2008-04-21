/**
 * @author Lar
 * This tests how the nxt brick deals with referenced objects from other classes
 * 
 */
package test;

public class ObjectMain {

	public static void main(String [] args){
		
		TestObject t = new TestObject(6);
		while (true)
		t.print();
		
	}
}
