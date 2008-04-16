//myTestMain.java Test Class
//@author Patrick McDonagh
public class myTestMain {

	
	public static void main(String[] args) {
		
		//test values to use
		//
		long barcode = 5;
		String name = "Peter V. Gibney";
		String emailaddress = "peter.gibney@ucdconnect.ie";
		int phonenumber = 1234575;
		int customerid = 2;
		

		//Various Test Code Placed Here
		
	
		//1. Creates a Query For a Product and prints out returned data
		//ItemQuery myItem = new ItemQuery(barcode);
		//System.out.println("Product Barcode is: " +barcode);
		//System.out.println("Product Name is: " +myItem.name);
		//System.out.println("Product Price is: "+myItem.price);
		//System.out.println("Product Minimum Weight is: "+myItem.minweight+"g");
		
		
		//2. Creates a new customer in the database
		//createCustomer myCST = new createCustomer(name, emailaddress, phonenumber);
		
		//3. Retrieve a customer from the database
//		getCustomer myReturnedCustomer = new getCustomer(2);
//		System.out.println("Name = "+myReturnedCustomer.myname);
//		System.out.println("Email Address is: "+myReturnedCustomer.myemailaddress);
//		System.out.println("Phone Number is: "+myReturnedCustomer.myphonenumber);
		
		//4. Retrieve a recipe for a given item
		//getRecipe myNewRecipe = new getRecipe(barcode);
		//System.out.println("Recipe Name: "+myNewRecipe.recipename);
		//System.out.println("Other Ingredients Required: "+myNewRecipe.otheringredients);
		//System.out.println("How to make: "+myNewRecipe.instructions);
		
		//5. Retrieve a Reminder Object for a given customerID
		//getReminder myReminder = new getReminder();
		//String[] myarray = new String[10];
		//myarray = myReminder.returnReminder(5);
		
//		for(int i=0; i<=9; i++)
//		{
//			System.out.println(myarray[i]);
//		}
		
		
		//6. Add reminder to database
		int id = 3;
		String[] toBeAdded = new String[10];
		toBeAdded[0] = "i like";
		toBeAdded[1] = "food";
		//System.out.println(toBeAdded[2]);
		
		addReminder theReminder = new addReminder(id, toBeAdded);
		
			
		//System.out.println("GREAT SUCCESS");
	}

}

