package selfCheckOut.hardWareInterface;
/**
 * This  class is used to hold a Barcodes and weights
 *  for the SelfChekcOut project.
 * <p>
 * 
 * @author Peter Gibney
 * @version 30th March 2008.
 */
import selfCheckOut.BarCode;
import selfCheckOut.Weight;


public class HardWareResult {

	private BarCode[] barCodes = null;
	private Weight weight1 = null;
	private Weight weight2 = null;
	int numBarCodes = 0;
	
	public HardWareResult(BarCode[] barCodes,
							Weight weight1,
							Weight weight2) {
		this.weight1 = weight1;
		this.weight2 = weight2;
		this.barCodes = barCodes; 
		numBarCodes = this.barCodes.length;
		//System.out.println("Hello from Hardware results");
	}

	public BarCode[] getBarCodes() {
		return this.barCodes;
	}

	public Weight getWeight(int item) {
		Weight tempWeight = null;
		if (item == 1) {
			tempWeight = this.weight1;
		} else {
			tempWeight = this.weight2;
		}
		return tempWeight;
	}
}