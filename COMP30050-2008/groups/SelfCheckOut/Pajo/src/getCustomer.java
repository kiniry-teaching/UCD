//Product Query.java class designed to create a new product object,
//create query based on a barcode, return all necessary data,
//eliminates need for two seperate classes, replaces Product.java and 
//Query.java

import java.sql.*;

public class getCustomer {
 String myname;
 String myemailaddress;
 int myphonenumber;
	
		public getCustomer (int CustomerID) {
		try{
			Class.forName("com.mysql.jdbc.Driver").newInstance();
			String url  = "jdbc:mysql://localhost:3306/SelfCheckout";
			Connection conn = DriverManager.getConnection(url, "me", "pass");
			//Two Following prints are verification data
			//System.out.println("URL: " +url);
			//System.out.println("Connection: " +conn);
			//System.out.println("CONNECTED TO DATABASE");
			System.out.println("");
			
			
			Statement stmt = conn.createStatement();
			ResultSet rs;
			
			
			rs = stmt.executeQuery("SELECT Name,EmailAddress,PhoneNumber FROM Customers WHERE CustomerID = "+CustomerID+"");
			
			while ( rs.next() ) {
				myname = rs.getString("Name");
				myemailaddress = rs.getString("EmailAddress");
				myphonenumber = rs.getInt("PhoneNumber");
				
				
			}
					
		
			conn.close();
			//System.out.println("CONNECTION TERMINATED");
		} 
		catch (Exception e) {
			System.err.println("Got an Exception");
			System.err.println(e.getMessage());
			}
		
	}
	
	

}
