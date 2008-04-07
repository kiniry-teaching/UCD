//Product.java - Defines a Product object
//@author Patrick McDonagh
public class Product
{
	//member variables for each product attribute
	protected double num;
	double barcode;
	String name;
	int price;
	int weight;
	
	
	public Product(double bcode){
		this.num = bcode;
		
		//method calls to Query.java to get data for product
		barcode = Query.getBarcode(num);
		name = Query.getName(num);
		price = Query.getPrice(num);
		weight = Query.getWeight(num);
	}
	
	
}
