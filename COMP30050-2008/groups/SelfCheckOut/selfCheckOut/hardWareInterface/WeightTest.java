package selfCheckOut.hardWareInterface;


//to run:

//C:\DN008\3rdYear\Sem.2\COMP30050\WS\SelfCheckOut\bin>java -ea 
// selfCheckOut.hardWareInterface.WeightTest


import selfCheckOut.Weight;
import java.util.Scanner;

public class WeightTest {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		Weight testWeight1 = new Weight(999);
			
		String repStr = testWeight1.exportWeight();
		
		System.out.println(repStr);
		
		Scanner inScan = new Scanner(repStr);
		
		Weight testWeight2 = Weight.importWeight(inScan);
		
		System.out.println(testWeight2);
		
		System.out.println(testWeight2.exportWeight());
		System.out.println(testWeight2.equals(testWeight1));

	}

}
