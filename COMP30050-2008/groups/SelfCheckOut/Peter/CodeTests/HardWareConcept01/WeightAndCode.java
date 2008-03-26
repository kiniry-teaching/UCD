
public class WeightAndCode {
	private int weight1;
	private int weight2;
	private int code;
	// ------------------------------------------------------	
	public WeightAndCode(int w1, int w2, int code) {
		assert w1 >= 0;
		assert w2 >= 0;
		weight1 = w1;
		weight2 = w2;
		this.code = code;
	}
	// ------------------------------------------------------
	public int getWeight(int w){
		int tempWeight;
		if (w == 1) {
			tempWeight = weight1; 
		} else {
			tempWeight = weight2;
		}
		return tempWeight;
	}
	// ------------------------------------------------------
	public int getCode(){
		return code;
	}
}
