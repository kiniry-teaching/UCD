//ItemQuery.java class designed to create a new product object,
//create query based on a barcode, return all necessary data,
//eliminates need for two seperate classes, replaces Product.java and 
//Query.java

import java.sql.*;

public class ItemQuery {
	String name;
	int price;
	int minweight;
	//Barcode bcode;
	

	//public ItemQuery (BarCode bc)
	//
	
	
	public ItemQuery (long barcode) {
		try{
			Class.forName("com.mysql.jdbc.Driver").newInstance();
			
			//String url  = "jdbc:mysql://sql104.hostwq.net:3306/hq_1793448_SelfCheckout";
			String url  = "jdbc:mysql://169.254.117.255:3306/SelfCheckout";
			//String url  = "jdbc:mysql://localhost:3306/SelfCheckout";
			//Connection conn = DriverManager.getConnection(url, "hq_1793448", "password");
			Connection conn = DriverManager.getConnection(url, "me", "pass");
			//Two Following prints are verification data
			//System.out.println("URL: " +url);
			//System.out.println("Connection: " +conn);
			//System.out.println("CONNECTED TO DATABASE");
			System.out.println("");
			
			
			Statement stmt = conn.createStatement();
			ResultSet rs;
			
			//rs = stmt.executeQuery("SELECT Name,Price,MinWeight FROM Items WHERE Barcode = "+bc.asLong +"");
			rs = stmt.executeQuery("SELECT Name,Price,MinWeight FROM Items WHERE Barcode = "+barcode +"");
			
			while ( rs.next() ) {
				name = rs.getString("Name");
				price = rs.getInt("Price");
				minweight = rs.getInt("MinWeight");
				
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
