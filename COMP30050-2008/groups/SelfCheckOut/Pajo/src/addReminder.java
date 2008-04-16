import java.sql.*;

public class addReminder {

	public addReminder (int custID, String[] reminderarray) {
		try{
			Class.forName("com.mysql.jdbc.Driver").newInstance();
			String url  = "jdbc:mysql://localhost:3306/SelfCheckout";
			Connection conn = DriverManager.getConnection(url, "me", "pass");
			//Two Following prints are verification data
			//System.out.println("URL: " +url);
			//System.out.println("Connection: " +conn);
			//System.out.println("CONNECTED TO DATABASE");
			System.out.println("");
			
			
			PreparedStatement pstmt = conn.prepareStatement("INSERT INTO Reminder(CustomerID,Item1BC,Item2BC,Item3BC,Item4BC,Item5BC,Item6BC,Item7BC,Item8BC,Item9BC,Item10BC) VALUES(?,?,?,?,?,?,?,?,?,?,?)");
			pstmt.setInt(1, custID);
			pstmt.setString(2, reminderarray[0]);
			pstmt.setString(3, reminderarray[1]);
			pstmt.setString(4, reminderarray[2]);
			pstmt.setString(5, reminderarray[3]);
			pstmt.setString(6, reminderarray[4]);
			pstmt.setString(7, reminderarray[5]);
			pstmt.setString(8, reminderarray[6]);
			pstmt.setString(9, reminderarray[7]);
			pstmt.setString(10, reminderarray[8]);
			pstmt.setString(11, reminderarray[9]);
			
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
