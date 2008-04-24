package selfCheckOut.hardWareInterface;
/**
	 * This  class is used to test some of the members of the class BarCode 
	 * for the Hardware interface components of the SelfChekcOut project.
	 * <p>
	 * @author Peter Gibney
	 * @version 16th March 2008.
	 */

//to run: 

//C:\DN008\3rdYear\Sem.2\COMP30050\WS\SelfCheckOut\bin>java -ea 
//selfCheckOut.hardWareInterface.BarCodeTest01



import java.util.Scanner;
import java.util.concurrent.TimeUnit;

import selfCheckOut.BarCode;
import selfCheckOut.Weight;

public class BarCodeTest01 {

	public static void wasteTime() {
		try {
			Thread.sleep(25);
		} catch (InterruptedException e) {
			System.err.println("Exception ScalesClient..");
			e.printStackTrace();
		}
	}
	
	public static void main(String args[]) {
		System.out.println(" ");
		System.out.println(" ----------- BarCode tester ------------------- ");
		System.out.println(" ");
		
		String testStr = "123456789012"; //note one char too short 
		BarCode testCode01 = null;
		System.out.println(" ----------------A---------------- ");
		wasteTime();
		try {
			//this should fail
			testCode01 = new BarCode(testStr);
		} catch (Exception e) {
			System.out.println("BarCode()exception = " + e.toString());
			System.out.println("This is supposed to fail");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
		}
		System.out.println(" ----------------B---------------- ");
		wasteTime();
		try {
			//this should fail
			testCode01 = new BarCode(testStr + "A");
		} catch (Exception e) {
			System.out.println("BarCode()exception = " + e.toString());
			System.out.println("This is supposed to fail");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
		}
		System.out.println(" ----------------C---------------- ");
		wasteTime();
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
		System.out.println(" ----------------D---------------- ");
		wasteTime();
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
		System.out.println(" ---------------E---------------- ");
		System.out.println(" ");
		System.out.println("Should be equal: [true] " + testCode01.equals(testCode01));
		if (testCode01.equals(testCode01) != true) {
			System.out.println("ERROR Should be equal: [true]" + 
					testCode01.equals(testCode01));
		}
		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		wasteTime();
		//this should not indicate equality
		BarCode testCode02 = new BarCode(testCode01.getNumbers());
		System.out.println(" ----------------F--------------- ");
		System.out.println(" ");
		System.out.println("Should be _NOT_ be equal (false): " 
				+ testCode01.equals(testCode02));
		if (testCode01.equals(testCode02) != false) {
			System.out.println("ERROR Should be _NOT_ be equal (false): " + 
					testCode01.equals(testCode01));
		}
		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		//this should indicate same code value
		System.out.println(" -----------------G--------------- ");
		System.out.println(" ");
		System.out.println("Should be same value: [TRUE] " + 
				testCode01.sameBarCodeValue(testCode01));
		if (testCode01.sameBarCodeValue(testCode01) != true) {
			System.out.println("ERROR Should be same value: [TRUE] " + 
					testCode01.equals(testCode01));
		}
		System.out.println(" ");
		System.out.println(" -------------------------------- ");

		//this should indicate same code value
		System.out.println(" ----------H---------------------- ");
		System.out.println(" ");
		System.out.println("Should be same value:[true] " + 
				testCode01.sameBarCodeValue(testCode02));
		if (testCode01.sameBarCodeValue(testCode02) != true) {
			System.out.println("ERROR Should be same value: [TRUE] " + 
					testCode01.sameBarCodeValue(testCode02));
		}
		
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
		System.out.println(" -----------I--------------------- ");
		wasteTime();
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
		System.out.println(" ----------------J---------------- ");
		wasteTime();
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
		System.out.println(" ----------------K---------------- ");
		wasteTime();
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
		System.out.println(" ----------------L---------------- ");
		System.out.println(" ");
		System.out.println("Should be equal:[TRUE] " + testCode03.equals(testCode03));
		if (!testCode03.equals(testCode03)) {
			System.out.println("ERROR! Should be equal:[TRUE] " + testCode03.equals(testCode03));
		}
		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		//this should not indicate equality
		wasteTime();
		BarCode testCode04 = new BarCode(testCode03.getNumbers());
		System.out.println(" -----------------M--------------- ");
		System.out.println(" ");
		System.out.println("Should be _NOT_ be equal (false): " 
				+ testCode03.equals(testCode04));
		if (testCode03.equals(testCode04)) {
			System.out.println("ERROR !Should be _NOT_ be equal (false): " 
					+ testCode03.equals(testCode04));
		}
		
		System.out.println(" ");
		System.out.println(" -------------------------------- ");

		
		//this should not indicate equality
		System.out.println(" -----------------M2--------------- ");
		System.out.println(" ");
		System.out.println("Should be Same value (true): " 
				+ testCode03.sameBarCodeValue(testCode04));
		if (!testCode03.sameBarCodeValue(testCode04)) {
			System.out.println("ERROR !Should be SAME  (true): " 
					+ testCode03.sameBarCodeValue(testCode04));
		}
		
		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		
		//this should indicate same code value
		System.out.println(" --------------N------------------ ");
		System.out.println(" ");
		System.out.println("Should be same value: [TRUE] " + 
				testCode03.sameBarCodeValue(testCode03));
		if (!testCode03.sameBarCodeValue(testCode03)) {
			System.out.println("ERROR! Should be same value: [TRUE] " + 
					testCode03.sameBarCodeValue(testCode03));
		}
		System.out.println(" ");
		System.out.println(" -------------------------------- ");

		//this should indicate same code value
		System.out.println(" ---------------O----------------- ");
		System.out.println(" ");
		System.out.println("Should be same value:[TRUE] " + 
				testCode03.sameBarCodeValue(testCode04));
		if (!testCode03.sameBarCodeValue(testCode04)) {
			System.out.println("ERROR! Should be same value:[TRUE] " + 
					testCode03.sameBarCodeValue(testCode04));
		}
		System.out.println(" ");
		System.out.println(" -------------------------------- ");

		//this should indicate same code value
		System.out.println(" ----------------P---------------- ");
		System.out.println(" ");
		System.out.println("Should be same value: [TRUE] " + 
				testCode01.sameBarCodeValue(testCode04));
		if (!testCode01.sameBarCodeValue(testCode04)) {
			System.out.println("ERROR! Should be same value:[TRUE] " + 
					testCode01.sameBarCodeValue(testCode04));
		}
		
		System.out.println(" ---------Q----------------------- ");
		System.out.println("Should be same value:  [TRUE] " + 
				testCode02.sameBarCodeValue(testCode04));
		if (!testCode02.sameBarCodeValue(testCode04)) {
			System.out.println("ERROR! Should be same value:  [TRUE] " + 
					testCode02.sameBarCodeValue(testCode04));
		}
		System.out.println(" ------R-------------------------- ");
		System.out.println("Should be same value:  [TRUE] " + 
				testCode02.sameBarCodeValue(testCode03));
		if (!testCode02.sameBarCodeValue(testCode03)) {
			System.out.println("ERROR! Should be same value:  [TRUE] "  + 
					testCode02.sameBarCodeValue(testCode03));
		}
		System.out.println(" ---------S----------------------- ");
		System.out.println("Should be same value: [TRUE]  " + 
				testCode01.sameBarCodeValue(testCode03));
		if (!testCode01.sameBarCodeValue(testCode03)) {
			System.out.println("ERROR! Should be same value: [TRUE]  " + 
					testCode01.sameBarCodeValue(testCode03));
		}
		System.out.println(" ---------S2----------------------- ");
		System.out.println("Should be same value: [TRUE]  " + 
				testCode03.sameBarCodeValue(testCode01));
		if (!testCode03.sameBarCodeValue(testCode01)) {
			System.out.println("ERROR! Should be same value: [TRUE]  " + 
					testCode03.sameBarCodeValue(testCode01));
		}
		System.out.println(" ---------S3----------------------- ");
		System.out.println("Should be same value: [TRUE]  " + 
				testCode01.sameBarCodeValue(testCode01));
		if (!testCode01.sameBarCodeValue(testCode01)) {
			System.out.println("ERROR! Should be same value: [TRUE]  " + 
					testCode01.sameBarCodeValue(testCode01));
		}

		
		System.out.println(" ");
		System.out.println(" -------------------------------- ");

		
		System.out.println(" -------------------------------- ");
		System.out.println(testCode03);
		System.out.println(" ");
		System.out.println(testCode04);
		System.out.println(" -------------------------------- ");
		System.out.println(" --------------T------------------ ");
		//this should indicate equality
		wasteTime();
		BarCode testCode05 = new BarCode(testCode03.getNumbers(),
								testCode03.getProbability(),
								testCode03.getTimeStamp());
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		System.out.println("!!Should be equal:(true): " + 
				testCode03.equals(testCode05));
		if (!testCode03.equals(testCode05)) {
			System.out.println("ERROR!  !Should be equal:(true): " + 
					testCode03.equals(testCode05));
		}

		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		//this should not indicate equality
		testCode05 = null;
		System.out.println(" ---------------U----------------- ");
		System.out.println(" ");
		System.out.println("!!Should _NOT_ be equal:(false): " + testCode03.equals(testCode05));
		if (testCode03.equals(testCode05)) {
			System.out.println("ERROR! !!Should _NOT_ be equal:(false): " + 
					testCode03.equals(testCode05));
		}

		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		//this should not indicate SameValue
		testCode05 = null;
		System.out.println(" ---------------V----------------- ");
		System.out.println(" ");
		System.out.println("!!Should _NOT_ be same:(false): " + testCode03.sameBarCodeValue(testCode05));
		if (testCode03.sameBarCodeValue(testCode05)) {
			System.out.println("ERROR! !!Should _NOT_ be same:(false): " + 
					testCode03.sameBarCodeValue(testCode05));
		}

		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		
		//this should not indicate SameValue
		testCode05 = null;
		testStr = "234567890129"; //note one char too short 
		// add on the correct check digit
		testStr = testStr + BarCode.getPotentialCheckDigit(testStr); 
		testCode05 = new BarCode(testStr);
		System.out.println(" ---------------W----------------- ");
		System.out.println(" ");
		System.out.println("!!Should _NOT_ be same:(false): " + testCode03.sameBarCodeValue(testCode05));
		if (testCode03.sameBarCodeValue(testCode05)) {
			System.out.println("ERROR! !!Should _NOT_ be same:(false): " + 
					testCode03.sameBarCodeValue(testCode05));
		}

		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		System.out.println(" ---------------X----------------- ");
		System.out.println(" ");
		System.out.println("!!Should _NOT_ be same:(false): " + testCode05.sameBarCodeValue(testCode03));
		if (testCode05.sameBarCodeValue(testCode03)) {
			System.out.println("ERROR! !!Should _NOT_ be same:(false): " + 
					testCode05.sameBarCodeValue(testCode03));
		}

		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		System.out.println(" ");
		
		String repStr = testCode05.exportBarCode();
		
		System.out.println(repStr);
		
		Scanner inScan = new Scanner(repStr);
		
		BarCode testCode06 = BarCode.importBarCode(inScan);
		
		System.out.println(testCode06);
		
		System.out.println(testCode06.exportBarCode());
		System.out.println(testCode06.equals(testCode05));
		
	}
}