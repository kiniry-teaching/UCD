package ie.ucd.music.comparison.Database;

import java.sql.*;

/**
 *
 * @author WheloStuff
 *
 */
public class InsertValues {
    static String blah;
    public void insertInfo(String artistName, String songTitle, int bitRate, String library1){
        try {
            Class.forName("com.mysql.jdbc.Driver").newInstance();
            String url = "jdbc:mysql://localhost:3306/Music";
            Connection conn = DriverManager.getConnection(url, "root", "");
            PreparedStatement mystmt = conn.prepareStatement("INSERT INTO " + library1 + "(Artist_Name,Track_Title,Bit_Rate) VALUES(?,?,?)");
            mystmt.setString(1,artistName);
            mystmt.setString(2,songTitle);
            mystmt.setInt(3, bitRate);
        
            mystmt.executeUpdate();
      
            conn.close();
            }
        catch (Exception e)
        {
            e.printStackTrace();
        }
   // return blah;
    }
    
}