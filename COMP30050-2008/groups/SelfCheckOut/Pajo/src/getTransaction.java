//returns a transaction

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.Statement;

public class getTransaction {

	static int transaxID;
	static String[] basket= new String[10];
	
		

	public getTransaction (int custid) {
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
			
			
			rs = stmt.executeQuery("SELECT TransactionID,Item1,Item2,Item3,Item4,Item5,Item6,Item7,Item8,Item9,Item10 FROM Transactions WHERE CustID = "+custid+"");
			
			while ( rs.next() ) {
				transaxID = rs.getInt("TransactionID");
				basket[0]=rs.getString("Item1");
				basket[1]=rs.getString("Item2");
				basket[2]=rs.getString("Item3");
				basket[3]=rs.getString("Item4");
				basket[4]=rs.getString("Item5");
				basket[5]=rs.getString("Item6");
				basket[6]=rs.getString("Item7");
				basket[7]=rs.getString("Item8");
				basket[8]=rs.getString("Item9");
				basket[9]=rs.getString("Item10");
				
				
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