//getReminder - allows for the retrieval of reminders set by a specific customer


import java.sql.*;

public class getReminder {
static String[] reminderarray= new String[10];
	
		

	public String[] returnReminder(int custid) {
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
			
			
			rs = stmt.executeQuery("SELECT Item1BC,Item2BC,Item3BC,Item4BC,Item5BC,Item6BC,Item7BC,Item8BC,Item9BC,Item10BC FROM Reminder WHERE CustomerID = "+custid+"");
			
			while ( rs.next() ) {
				reminderarray[0]=rs.getString("Item1BC");
				reminderarray[1]=rs.getString("Item2BC");
				reminderarray[2]=rs.getString("Item3BC");
				reminderarray[3]=rs.getString("Item4BC");
				reminderarray[4]=rs.getString("Item5BC");
				reminderarray[5]=rs.getString("Item6BC");
				reminderarray[6]=rs.getString("Item7BC");
				reminderarray[7]=rs.getString("Item8BC");
				reminderarray[8]=rs.getString("Item9BC");
				reminderarray[9]=rs.getString("Item10BC");
				
				
			}
			conn.close();		
			
			
			//System.out.println("CONNECTION TERMINATED");
		} 
		catch (Exception e) {
			System.err.println("Got an Exception");
			System.err.println(e.getMessage());
			}
		return reminderarray;
		
	}
	
	

}