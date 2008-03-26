	/**
	 * This  class is used to test the class Digit for the Hardware interface 
	 * components of the SelfChekcOut project.
	 * <p>
	 * @author Peter Gibney
	 * @version 25th March 2008.
	 */
public class BarCodeTest01 {


	public static void main(String args[]) {
		Barcode testCode01 = new Barcode("1234567890123");
		System.out.println(" testCode01 = " + testCode01);
		System.out.println(" -------------------------------- ");
		Barcode testCode02 = new Barcode(testCode01.getNumbers());
		System.out.println(" testCode02 = " + testCode02);
		System.out.println(" -------------------------------- ");
		//Barcode testCode03 = new Barcode("12345A7890123");
		//System.out.println(" testCode03 = " + testCode03);
		//System.out.println(" -------------------------------- ");

		
		
		BarNums testNums01 = new BarNums(testCode01.getNumbers());
		System.out.println(" testNums01 = " + testNums01);
		System.out.println(" -------------------------------- ");
		
		
		int[] barInts = testCode01.getNumbers();
		barInts[4] = barInts[4] + 10;
		//Barcode testCode04 = new Barcode(barInts);
		//System.out.println(" testCode04 = " + testCode04);
		
		BarNums testNums02 = new BarNums(barInts);
		System.out.println(" testNums02 = " + testNums02);
		System.out.println(" -------------------------------- ");
		Barcode testCode05 = new Barcode(testNums02.getNumbers(true));
		System.out.println(" testCode05 = " + testCode05);
		System.out.println(" -------------------------------- ");
		
	}
}