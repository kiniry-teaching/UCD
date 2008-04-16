//getRecipe - class to a get a recipe based on items bought

import java.sql.*;

public class getRecipe {
 static String recipename;
 static String otheringredients;
 static String instructions;
	
		public getRecipe (long barcode) {
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
			
			
			rs = stmt.executeQuery("SELECT Name,OtherIngredients,Instructions FROM Recipes WHERE PrimeItemBC = "+barcode+"");
			
			while ( rs.next() ) {
				recipename = rs.getString("Name");
				otheringredients = rs.getString("OtherIngredients");
				instructions = rs.getString("Instructions");
				
				
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

