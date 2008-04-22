//createCustomer allows for the creation of a new customer, allows creates
//a new unique reminder for that customer

import java.sql.*;

public class createCustomer {

	
		public createCustomer (String Name, String EmailAddress, int PhoneNumber) {
		try{
			Class.forName("com.mysql.jdbc.Driver").newInstance();
			String url  = "jdbc:mysql://localhost:3306/SelfCheckout";
			Connection conn = DriverManager.getConnection(url, "me", "pass");
			//Two Following prints are verification data
			//System.out.println("URL: " +url);
			//System.out.println("Connection: " +conn);
			//System.out.println("CONNECTED TO DATABASE");
			System.out.println("");
			
			
			PreparedStatement pstmt = conn.prepareStatement("INSERT INTO Customers(Name,EmailAddress,PhoneNumber) VALUES(?,?,?)");
			pstmt.setString(1, Name);
			pstmt.setString(2, EmailAddress);
			pstmt.setInt(3, PhoneNumber);
			
			pstmt.executeUpdate();
			
			System.out.println("Insertion Complete.");
			
			PreparedStatement pstmt1 = conn.prepareStatement("INSERT INTO Reminder(Item1BC) VALUES(?)");
			pstmt1.setString(1, null);
			System.out.println("Insertion Complete.");
			
			pstmt1.executeUpdate();
			
			
			
			conn.close();
			//System.out.println("CONNECTION TERMINATED");
		} 
		catch (Exception e) {
			System.err.println("Got an Exception");
			System.err.println(e.getMessage());
			}
		
	}
	
	

}