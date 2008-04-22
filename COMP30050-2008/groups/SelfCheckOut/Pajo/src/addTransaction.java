//adds a transaction to the database for the specified customerID

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;

public class addTransaction {

	public addTransaction(int custID, String[] basket) {
		try{
			Class.forName("com.mysql.jdbc.Driver").newInstance();
			String url  = "jdbc:mysql://localhost:3306/SelfCheckout";
			Connection conn = DriverManager.getConnection(url, "me", "pass");
			//Two Following prints are verification data
			//System.out.println("URL: " +url);
			//System.out.println("Connection: " +conn);
			//System.out.println("CONNECTED TO DATABASE");
			System.out.println("");
			
			
			PreparedStatement pstmt = conn.prepareStatement("INSERT INTO Transactions(CustID,Item1,Item2,Item3,Item4,Item5,Item6,Item7,Item8,Item9,Item10) VALUES(?,?,?,?,?,?,?,?,?,?,?)");
			pstmt.setInt(1, custID);
			pstmt.setString(2, basket[0]);
			pstmt.setString(3, basket[1]);
			pstmt.setString(4, basket[2]);
			pstmt.setString(5, basket[3]);
			pstmt.setString(6, basket[4]);
			pstmt.setString(7, basket[5]);
			pstmt.setString(8, basket[6]);
			pstmt.setString(9, basket[7]);
			pstmt.setString(10, basket[8]);
			pstmt.setString(11, basket[9]);
			
			pstmt.executeUpdate();
					
			System.out.println("Insertion Complete.");
			conn.close();
			//System.out.println("CONNECTION TERMINATED");
		} 
		catch (Exception e) {
			System.err.println("Got an Exception");
			System.err.println(e.getMessage());
			}
		
	}













}

