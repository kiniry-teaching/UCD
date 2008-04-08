//myTestMain.java Test Class
//@author Patrick McDonagh
public class myTestMain {

	
	public static void main(String[] args) {
		
		//test values to use
		//
		double barcode = 2;
		String name = "Joe Bloggs";
		String emailaddress = "joebloggsgmail.com";
		int phonenumber = 1234567;
		int customerid = 2;
		

		//Various Test Code Placed Here
		
	
		//1. Creates a Query For a Product and prints out returned data
//		ItemQuery myItem = new ItemQuery(barcode);
//		System.out.println("Product Barcode is: " +barcode);
//		System.out.println("Product Name is: " +myItem.name);
//		System.out.println("Product Price is: "+myItem.price);
//		System.out.println("Product Weight is: "+myItem.minweight+"g");
		
		
		//2. Creates a new customer in the database
		//createCustomer myCST = new createCustomer(name, emailaddress, phonenumber);
		
		//3. Retrieve a customer from the database
		getCustomer myReturnedCustomer = new getCustomer(2);
		System.out.println("Name = "+myReturnedCustomer.myname);
		System.out.println("Email Address is: "+myReturnedCustomer.myemailaddress);
		System.out.println("Phone Number is: "+myReturnedCustomer.myphonenumber);
			
		//System.out.println("GREAT SUCCESS");
	}

}

