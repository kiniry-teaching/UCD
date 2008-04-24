package selfCheckOut.hardWareInterface;
/**
	 * This  class is used to test the class Digit for the Hardware interface 
	 * components of the SelfChekcOut project.
	 * <p>
	 * @author Peter Gibney
	 * @version 23rd March 2008.
	 */
public class DigitTest03 {


	private static final double[][] KEY_CODES = 	
		{{300, 200, 100, 100},
		{200, 200, 200, 100},
		{200, 100, 200, 200},
		{100, 400, 100, 100},
		{100, 100, 300, 200},
		{100, 200, 300, 100},
		{100, 100, 100, 400},
		{100, 300, 100, 200},
		{100, 200, 100, 300},
		{300, 100, 100, 200},
		{100, 100, 200, 300},
		{100, 200, 200, 200},
		{200, 200, 100, 200},
		{100, 100, 400, 100},
		{200, 300, 100, 100},
		{100, 300, 200, 100},
		{400, 100, 100, 100},
		{200, 100, 300, 100},
		{300, 100, 200, 100},
		{200, 100, 100, 300}};


	private static int ODD_AND_EVEN = 0;
	private static int EVENS = 1;
	private static int ODDS = 2;

	public static void main(String args[]) {
		System.out.println("------------------------------------------");
		for (int i = 0; i < 20; i++) {
			boolean feedEven = (i >=10);
			Digit resultDigit = new Digit(ODD_AND_EVEN, KEY_CODES[i]);
			if ((feedEven != resultDigit.isEven()) || (i != resultDigit.getDigit())) {
				if (feedEven != resultDigit.isEven())
					System.out.println("	Evenness Error for i= " + i +
						", testing O&E, Num= " + resultDigit.getDigit() +
						", evenResult= " + resultDigit.isEven() +
						", sending even = " + (i >=10));
				if (i != resultDigit.getDigit())
					System.out.println("	Numerical Error for i= " + i +
						", testing O&E, Num= " + resultDigit.getDigit() +
						", evenResult= " + resultDigit.isEven() +
						", sending even = " + (i >=10));

			} else {
				System.out.println("O&E CorrectResponse for i = " + i + 
						", response = " + resultDigit.getDigit());
			}
		}
		System.out.println("------------------------------------------");
		for (int i = 0; i < 10; i++) {
			boolean feedEven = (i >=10);
			Digit resultDigit = new Digit(ODDS, KEY_CODES[i]);
			if ((feedEven != resultDigit.isEven()) || (i != resultDigit.getDigit())) {
				if (feedEven != resultDigit.isEven())
					System.out.println("	Evenness Error for i= " + i +
						", testing O, Num= " + resultDigit.getDigit() +
						", evenResult= " + resultDigit.isEven() +
						", sending even = " + (i >=10));
				if (i != resultDigit.getDigit())
					System.out.println("	Numerical Error for i= " + i +
						", testing O, Num= " + resultDigit.getDigit() +
						", evenResult= " + resultDigit.isEven() +
						", sending even = " + (i >=10));

			} else {
				System.out.println("O CorrectResponse for i = " + i + 
						", response = " + resultDigit.getDigit());
			}
		}
		System.out.println("------------------------------------------");
		for (int i = 10; i < 20; i++) {
			boolean feedEven = (i >=10);
			Digit resultDigit = new Digit(EVENS, KEY_CODES[i]);
			if ((feedEven != resultDigit.isEven()) || (i != resultDigit.getDigit())) {
				if (feedEven != resultDigit.isEven())
					System.out.println("	Evenness Error for i= " + i +
						", testing E, Num= " + resultDigit.getDigit() +
						", evenResult= " + resultDigit.isEven() +
						", sending even = " + (i >=10));
				if (i != resultDigit.getDigit())
					System.out.println("	Numerical Error for i= " + i +
						", testing E, Num= " + resultDigit.getDigit() +
						", evenResult= " + resultDigit.isEven() +
						", sending even = " + (i >=10));

			} else {
				System.out.println("E CorrectResponse for i = " + i + 
						", response = " + resultDigit.getDigit());
			}
		}
		System.out.println("------------------------------------------");
		//feed odd test agains evens
		for (int i = 0; i < 10; i++) {
			Digit resultDigit = new Digit(EVENS, KEY_CODES[i]);
			if ((resultDigit.isEven()) || (resultDigit.isOdd()) || (resultDigit.getDigit() != -1)) {
				if ((resultDigit.isEven()) || (resultDigit.isOdd()))
					System.out.println("	Evenness Error for i= " + i +
						", testing O, Num= " + resultDigit.getDigit() +
						", evenResult= " + resultDigit.isEven() +
						", sending even = " + (i >=10));
				if (resultDigit.getDigit() != -1)
					System.out.println("	Numerical Error for i= " + i +
						", testing O, Num= " + resultDigit.getDigit() +
						", evenResult= " + resultDigit.isEven() +
						", sending even = " + (i >=10));

			} else {
				System.out.println("CorrectResponse for i = " + i + 
						" sent odd tested against even, response = " + resultDigit.getDigit());
			}
		}

		System.out.println("------------------------------------------");
		//feed even test agains odd
		for (int i = 10; i < 20; i++) {
			Digit resultDigit = new Digit(ODDS, KEY_CODES[i]);
			if ((resultDigit.isEven()) || (resultDigit.isOdd()) || (resultDigit.getDigit() != -1)) {
				if ((resultDigit.isEven()) || (resultDigit.isOdd()))
					System.out.println("	Evenness Error for i= " + i +
						", testing O, Num= " + resultDigit.getDigit() +
						", evenResult= " + resultDigit.isEven() +
						", sending even = " + (i >=10));
				if (resultDigit.getDigit() != -1)
					System.out.println("	Numerical Error for i= " + i +
						", testing O, Num= " + resultDigit.getDigit() +
						", evenResult= " + resultDigit.isEven() +
						", sending even = " + (i >=10));

			} else {
				System.out.println("CorrectResponse for i = " + i + 
						" sent even tested against odd, response = " + resultDigit.getDigit());
			}
		}

		
		
	
	}
}