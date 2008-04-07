//Product Query.java class designed to create a new product object,
//create query based on a barcode, return all necessary data,
//eliminates need for two seperate classes, replaces Product.java and 
//Query.java

import java.sql.*;

public class ProductQuery {
	static String name;
	static int price;
	static int weight;
	
	
	
	public ProductQuery (double barcode) {
		try{
			Class.forName("com.mysql.jdbc.Driver").newInstance();
			String url  = "jdbc:mysql://localhost:3306/TestBase";
			Connection conn = DriverManager.getConnection(url, "me", "pass");
			//Two Following prints are verification data
			//System.out.println("URL: " +url);
			//System.out.println("Connection: " +conn);
			//System.out.println("CONNECTED TO DATABASE");
			System.out.println("");
			
			
			Statement stmt = conn.createStatement();
			ResultSet rs;
			
			
			rs = stmt.executeQuery("SELECT Name,Price,Weight FROM Products WHERE Barcode = "+barcode +"");
			
			while ( rs.next() ) {
				name = rs.getString("Name");
				price = rs.getInt("Price");
				weight = rs.getInt("Weight");
				
//				System.out.println("In Database");
//				System.out.println(returnedData);
				
				
				

				}
			conn.close();
			//System.out.println("CONNECTION TERMINATED");
		} 
		catch (Exception e) {
			System.err.println("Got an Exception");
			System.err.println(e.getMessage());
			}
		//return returnedName;
	}
	
	

}
