//myTestMain.java Test Class
//@author Patrick McDonagh
public class myTestMain {

	
	public static void main(String[] args) {
		
		//test values to use
		long barcode = 1;
		
		String name = "Han Solo";
		String emailaddress = "hansolo@starwars.com";
		int phonenumber = 125;
		int customerid = 2;
		int solosID = 7;
		
		int id = 0;
		String[] toBeAdded = new String[10];
		toBeAdded[0] = "Pasta";
		toBeAdded[1] = "Milk";
		

		//Various Test Code Placed Here
		
		
		BarCode myBarcode = new BarCode(9780131246461l);
		//1. Creates a Query For a Product and prints out returned data
		Item myItem = new Item(myBarcode);
		System.out.println("Product Barcode is: " +myItem.barcode.toString());
		System.out.println("Product Name is: " +myItem.name);
		System.out.println("Product Price is: "+myItem.price);
		System.out.println("Product Minimum Weight is: "+myItem.minweight+"g");
		System.out.println("Product Weight is: "+myItem.weight+"g");
		System.out.println("Product Max Weight is: "+myItem.maxweight+"g");
		System.out.println("Product Sound File is at: "+myItem.soundfile);
		System.out.println("Product Image File is at: "+myItem.imagefile);
		System.out.println("Product Associated Allergy :"+myItem.allergy);
		System.out.println("Product PrimeItem = "+myItem.primeitem);
		
		
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
//		getReminder myReminder = new getReminder();
//		String[] myarray = new String[10];
//		myarray = myReminder.returnReminder(5);
//		
//		for(int i=0; i<=9; i++)
//		{
//			System.out.println(myarray[i]);
//		}
		
		
		//6. Add reminder to database
		//System.out.println(toBeAdded[2]);
		//addReminder theReminder = new addReminder(id, toBeAdded);
		
		
		//7. add a sample transaction to database
		//addTransaction myTransaction = new addTransaction (id, toBeAdded);
			
		
		//8. Get a Transaction from the database
		//getTransaction myTransaction = new getTransaction(id);
		//System.out.println(myTransaction.transaxID);
		//System.out.println(myTransaction.basket[0]);
		//System.out.println(myTransaction.basket[1]);
		
		//9. Update Reminders for that Customer @Finish and Pay time
		//updateReminder finishandpay = new updateReminder(solosID, toBeAdded);
		


		
		//System.out.println("GREAT SUCCESS");
	}

}

