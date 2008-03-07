public class HardWareConceptTest01 {

	static ScalesAndBarCode myScalesAndBarCode = null;
	public static void main (String args[]) {
		myScalesAndBarCode = new ScalesAndBarCode();
		myScalesAndBarCode.start();
		WeightAndCode myWeightAndCode; 
		for (int i = 0; i < 50; i++) {
			for (int delay =0; delay < 100000000; delay++) { }
			myWeightAndCode = myScalesAndBarCode.getWeightsAndCode();

			System.out.println("S1= " + myWeightAndCode.getWeight(1));
			System.out.println("Code= " + myWeightAndCode.getCode());
			System.out.println("S2= " + myWeightAndCode.getWeight(2));
			System.out.println("------------------------------");
		}
		myScalesAndBarCode.done();
	}
}
