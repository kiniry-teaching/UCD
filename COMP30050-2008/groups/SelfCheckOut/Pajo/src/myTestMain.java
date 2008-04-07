//myTestMain.java Test Class
//@author Patrick McDonagh
public class myTestMain {

	
	public static void main(String[] args) {
		
		//test value to use
		double barcode = 3;
		
		//create a new Product object
//		Product myProduct = new Product(barcode);
//		
//		//Test print outs of Product member variables
//		System.out.println("Product Barcode is: " +myProduct.barcode);
//		System.out.println("Product Name is: " +myProduct.name);
//		System.out.println("Product Price is: "+myProduct.price);
//		System.out.println("Product Weight is: "+myProduct.weight+"g");
		
		ProductQuery myPQ = new ProductQuery(barcode);
		
		System.out.println("Barcode is: "+barcode);
		System.out.println("Name is: "+ProductQuery.name);
		System.out.println("Price is: "+ProductQuery.price);
		System.out.println("Weight is: "+ProductQuery.weight);
		//System.out.println("GREAT SUCCESS");
	}

}

