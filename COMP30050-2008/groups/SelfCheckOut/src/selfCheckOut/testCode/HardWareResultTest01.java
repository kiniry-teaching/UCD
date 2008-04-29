package selfCheckOut.testCode;

import java.util.Scanner;
import selfCheckOut.BarCode;
import selfCheckOut.Weight;
import selfCheckOut.hardWareInterface.HardWareResult;

/**
 * This  class is used to test some of the members of the class HardWareResult 
 * for the Hardware interface components of the SelfChekcOut project.
 * <p>
 * @author Peter Gibney
 * @version 2nd April 2008.
 */


public class HardWareResultTest01 {

	
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		Weight testWeight1 = null;
		Weight testWeight2 = null;

		testWeight1 = new Weight(999);
		testWeight2 = new Weight(1500);
		
		BarCode[] barCodes = null;
		
		
		String testStr = "123456789012"; //note one char too short 
		testStr = testStr + BarCode.getPotentialCheckDigit(testStr);
		
		BarCode testCode01 = null;
		try {
			//this should not fail
			testCode01 = new BarCode(testStr);
		} catch (Exception e) {
			System.out.println("BarCode()exception = " + e.toString());
			System.out.println("This is _NOT_ supposed to fail");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
		}

		barCodes = new BarCode[25];
		for (int j = 0; j < barCodes.length; j++) {
			barCodes[j] = testCode01;
		}
		
		HardWareResult hwr1 = new HardWareResult(barCodes,
									testWeight1,
									testWeight2);
		
		String repStr = hwr1.exportHardWareResult();
		System.out.println(repStr);
		
		Scanner inScan = new Scanner(repStr);

		System.out.println(" ");
		System.out.println(" -------------------------------- ");
		System.out.println(" ");

		HardWareResult hwr2 = HardWareResult.importHardWareResult(inScan);
		if (hwr2 == null) {
			System.out.println("(hwr2 == null)");
		} else {
			System.out.println(" ");
			System.out.println(" -------------------------------- ");
			System.out.println(" ");
			
			repStr = hwr2.exportHardWareResult();
			System.out.println(repStr);
			
			System.out.println(" ");
			
			System.out.println("hwr1.equals(hwr2) " + hwr1.equals(hwr2));
			System.out.println(" ");
			
			System.out.println(hwr2.toString());
		}
	}
}
