//Query.java - Testing queries for test MySQL database
//@author Patrick McDonagh
import java.sql.*;

public class Query {

	//variables used for return data
	static String returnedName;
	static int returnedPrice;
	static int returnedWeight;
	static double returnedBarcode;
	
	//method to return Name based on a barcode
	public static String getName(double barcode) {
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
			
			
			rs = stmt.executeQuery("SELECT Name FROM Products WHERE Barcode = "+barcode +"");
			
			while ( rs.next() ) {
				returnedName = rs.getString("Name");
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
		return returnedName;
	}
	
	//method to return Price based on a barcode
	public static int getPrice(double barcode) {
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
			
			
			rs = stmt.executeQuery("SELECT Price FROM Products WHERE Barcode = "+barcode +"");
			
			while ( rs.next() ) {
				returnedPrice = rs.getInt("Price");
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
		return returnedPrice;
	}
	
	//method to return Weight in grams based on a barcode
	public static int getWeight(double barcode) {
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
			
			
			rs = stmt.executeQuery("SELECT Weight FROM Products WHERE Barcode = "+barcode +"");
			
			while ( rs.next() ) {
				returnedWeight = rs.getInt("Weight");
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
		return returnedWeight;
	}
	//method to return Barcode based on a barcode
	public static double getBarcode(double barcode) {
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
			
			
			rs = stmt.executeQuery("SELECT Barcode FROM Products WHERE Barcode = "+barcode +"");
			
			while ( rs.next() ) {
				returnedBarcode = rs.getDouble("Barcode");
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
		return returnedBarcode;
	}
	
	
}//end of Query.java class
