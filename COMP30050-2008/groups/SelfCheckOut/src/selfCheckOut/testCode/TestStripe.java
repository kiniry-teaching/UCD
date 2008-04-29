package selfCheckOut.testCode;
import selfCheckOut.hardWareInterface.BarCodeStripe;


/**
 * This class is used to test the BarCodeStripes.
 * <p>
 * @author Peter Gibney
 */

public class TestStripe {
	
	private static int[][] testBars = new int[100][2];

	public static void main(String[] args) {
		
		
		//fill testBars
		boolean toggleColour = true;
		for (int i=0; i < 100; i++) {
			int colour = 0;
			if (toggleColour) {
				colour = 0; // black
				toggleColour = false;
			} else {
				toggleColour = true;
				colour = 255; //white
			}
			testBars[i][0] = colour;
			testBars[i][1] = i + 1; //make the length = i+1
		}
		BarCodeStripe barCodeStripe = new BarCodeStripe(20, 0,  testBars);
		
		System.out.println("length = " + barCodeStripe.getLength());
		System.out.println("first pixel = " + barCodeStripe.getStart());
		System.out.println("middle pixel = " + barCodeStripe.getCentrePos());
		System.out.println("last pixel = " + barCodeStripe.getEnd());
		
		System.out.println("start middle space = " + barCodeStripe.getStartMiddleSpace());
		System.out.println("End middle space = " + barCodeStripe.getEndMiddleSpace());
	
	}

}
