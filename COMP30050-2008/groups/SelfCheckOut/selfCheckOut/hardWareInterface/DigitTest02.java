package selfCheckOut.hardWareInterface;
/**
	 * This  class is used to test the class Digit for the Hardware interface 
	 * components of the SelfChekcOut project.
	 * <p>
	 * 
	 * @author Peter Gibney
	 * @version 23rd March 2008.
	 */
public class DigitTest02 {

	private static final int[][] PARITY_TEST =
	{{0,0,0,0,0,1,0}, // 0, 0
	{0,0,0,0,1,0,-1}, // 1, -1
	{0,0,0,1,0,0,-1}, // 2, -1
	{0,0,0,1,1,0,-1}, // 3, -1
	{0,0,1,0,0,0,-1}, // 4, -1
	{0,0,1,0,1,0,-1}, // 5, -1
	{0,0,1,1,0,0,-1}, // 6, -1
	{0,0,1,1,1,0,-1}, // 7, -1
	{0,1,0,0,0,0,-1}, // 8, -1
	{0,1,0,0,1,0,-1}, // 9, -1
	{0,1,0,1,0,0,-1}, // 10, -1
	{0,1,0,1,1,1,1}, // 11, 1
	{0,1,1,0,0,0,-1}, // 12, -1
	{0,1,1,0,1,1,2}, // 13, 2
	{0,1,1,1,0,1,3}, // 14, 3
	{0,1,1,1,1,0,-1}, // 15, -1
	{1,0,0,0,0,0,-1}, // 16, -1
	{1,0,0,0,1,0,-1}, // 17, -1
	{1,0,0,1,0,0,-1}, // 18, -1
	{1,0,0,1,1,1,4}, // 19, 4
	{1,0,1,0,0,0,-1}, // 20, -1
	{1,0,1,0,1,1,7}, // 21, 7
	{1,0,1,1,0,1,8}, // 22, 8
	{1,0,1,1,1,0,-1}, // 23, -1
	{1,1,0,0,0,0,-1}, // 24, -1
	{1,1,0,0,1,1,5}, // 25, 5
	{1,1,0,1,0,1,9}, // 26, 9
	{1,1,0,1,1,0,-1}, // 27, -1
	{1,1,1,0,0,1,6}, // 28, 6
	{1,1,1,0,1,0,-1}, // 29, -1
	{1,1,1,1,0,0,-1}, // 30, -1
	{1,1,1,1,1,0,-1}}; // 31, -1

	
	public static void main(String args[]) {
		System.out.println("------------------------------------------");
		System.out.println("------------------------------------------");

		for (int i = 0; i < 32 ; i++) {
			boolean[] parityList = {false,false,false,false,false}; 
			//above line means nothing, just to get it to compile
			for (int j = 0; j < 5 ; j++) {
			 parityList[j] = (PARITY_TEST[i][j]==1);
			}
			Digit resultDigit = new Digit(parityList);
			
			if (resultDigit.getDigit() >=0) { 
				System.out.println("Correct Digit Parity test result, for i = "
						+ i +  ", result = " + " : " + resultDigit.getDigit() +
						", expecting : " + PARITY_TEST[i][6]);
			}
			if ((resultDigit.getDigit()>=0) && (PARITY_TEST[i][5]==0)){ 
				System.out.println("ERROR!! DigitParity test, " +
						"getting a num result for: i = " + i + 
						", result = " + resultDigit.getDigit() + 
						", expecting -1");
			}
			if (resultDigit.getDigit() != PARITY_TEST[i][6]){ 
				System.out.println("ERROR! Numerical Error, i = " + i + ", result = " +
					" : " + resultDigit.getDigit() +
					", expecting " + PARITY_TEST[i][6]);
			}
			if ((resultDigit.getDigit()==-1) && (PARITY_TEST[i][5]==1)){ 
				System.out.println("ParitysError, i = " + i + ", result = " +
					" : " + resultDigit.getDigit() +
					", expecting >= 0");
			}
		}
		System.out.println("------------------------------------------");
	}
}
