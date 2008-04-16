package selfCheckOut.hardWareInterface;
/**
	 * This  class is used to test some of the members of the class BarCode 
	 * for the Hardware interface components of the SelfChekcOut project.
	 * <p>
	 * @author Peter Gibney
	 * @version 16th March 2008.
	 */

import java.util.concurrent.TimeUnit;

import selfCheckOut.BarCode;

public class BarCodeTest01 {

	public static void main(String args[]) {
		System.out.println(" ");
		System.out.println(" ----------- BarCode tester ------------------- ");
		System.out.println(" ");
		
		String testStr = "123456789012"; //note one char too short 
		BarCode testCode01 = null;
		System.out.println(" -------------------------------- ");
		try {
			//this should fail
			testCode01 = new BarCode(testStr);
		} catch (Exception e) {
			System.out.println("BarCode()exception = " + e.toString());
			System.out.println("This is supposed to fail");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
		}
		try {
			//this should fail
			testCode01 = new BarCode(testStr + "A");
		} catch (Exception e) {
			System.out.println("BarCode()exception = " + e.toString());
			System.out.println("This is supposed to fail");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
		}
		try {
			//this should fail
			testCode01 = new BarCode("B" + testStr);
		} catch (Exception e) {
			System.out.println("BarCode()exception = " + e.toString());
			System.out.println("This is supposed to fail");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
		}
		// add on the correct check digit
		testStr = testStr + BarCode.getPotentialCheckDigit(testStr); 
		try {
			//this should not fail
			testCode01 = new BarCode(testStr);
		} catch (Exception e) {
			System.out.println("BarCode()exception = " + e.toString());
			System.out.println("This is _NOT_ supposed to fail");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
		}
		//this should indicate equality
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		System.out.println("Should be equal:" + testCode01.equals(testCode01));
		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		//this should not indicate equality
		BarCode testCode02 = new BarCode(testCode01.getNumbers());
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		System.out.println("Should be _NOT_ be equal (false):" 
				+ testCode01.equals(testCode02));
		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		//this should indicate same code value
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		System.out.println("Should be same value:" + 
				testCode01.sameBarCodeValue(testCode01));
		System.out.println(" ");
		System.out.println(" -------------------------------- ");

		//this should indicate same code value
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		System.out.println("Should be same value:" + 
				testCode01.sameBarCodeValue(testCode02));
		System.out.println(" ");
		System.out.println(" -------------------------------- ");

		System.out.println(" -------------------------------- ");
		System.out.println(testCode01);
		System.out.println(" ");
		System.out.println(testCode02);
		System.out.println(" -------------------------------- ");
		

		//--------------------------------------------------------------
		
		long testLong = 123456789012l; //note one digit too short 
		BarCode testCode03 = null;
		System.out.println(" -------------------------------- ");
		try {
			//this should fail
			testCode03 = new BarCode(testLong);
		} catch (Exception e) {
			System.out.println("BarCode()exception = " + e.toString());
			System.out.println("This is supposed to fail");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
		}
		// add on the correct check digit
		try {
			//this should not fail
			testCode03 = new BarCode((testLong * 10l)+ 
					BarCode.getPotentialCheckDigit(""+ testLong));
		} catch (Exception e) {
			System.out.println("BarCode()exception = " + e.toString());
			System.out.println("This is _NOT_ supposed to fail");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
		}
		// add on the correct check digit
		try {
			//this should not fail
			testCode03 = new BarCode((testLong * 10l)+ 
					BarCode.getPotentialCheckDigit(testLong));
		} catch (Exception e) {
			System.out.println("BarCode()exception = " + e.toString());
			System.out.println("This is _NOT_ supposed to fail");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
		}
		
		//this should indicate equality
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		System.out.println("Should be equal:" + testCode03.equals(testCode03));
		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		//this should not indicate equality
		BarCode testCode04 = new BarCode(testCode03.getNumbers());
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		System.out.println("Should be _NOT_ be equal (false):" 
				+ testCode03.equals(testCode04));
		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		//this should indicate same code value
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		System.out.println("Should be same value:" + 
				testCode03.sameBarCodeValue(testCode03));
		System.out.println(" ");
		System.out.println(" -------------------------------- ");

		//this should indicate same code value
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		System.out.println("Should be same value:" + 
				testCode03.sameBarCodeValue(testCode04));
		System.out.println(" ");
		System.out.println(" -------------------------------- ");

		//this should indicate same code value
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		System.out.println("Should be same value: " + 
				testCode01.sameBarCodeValue(testCode04));
		System.out.println("Should be same value: " + 
				testCode02.sameBarCodeValue(testCode04));
		System.out.println("Should be same value: " + 
				testCode02.sameBarCodeValue(testCode03));
		System.out.println("Should be same value: " + 
				testCode01.sameBarCodeValue(testCode03));
		System.out.println(" ");
		System.out.println(" -------------------------------- ");

		
		System.out.println(" -------------------------------- ");
		System.out.println(testCode03);
		System.out.println(" ");
		System.out.println(testCode04);
		System.out.println(" -------------------------------- ");
	}
}