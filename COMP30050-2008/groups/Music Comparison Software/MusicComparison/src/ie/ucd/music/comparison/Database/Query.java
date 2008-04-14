package ie.ucd.music.comparison.Database;
import java.awt.List;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

/**
 * Query class runs any query on the database.
 */
class Query {
    /**
     * This String returns the name.
     */
    private static String returnedName;
    public static void main(final String args[]) {
    private Connection conn;
    public Query() {
        
        
        try {
            Class.forName("com.mysql.jdbc.Driver").newInstance();

            String url = "jdbc:mysql://localhost:3306/Music";

            conn = DriverManager.getConnection(url, "root", "");
        } catch (InstantiationException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (IllegalAccessException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (ClassNotFoundException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (SQLException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    
        
    }
       System.out.println(""); 

     Statement stmt = conn.createStatement();

     ResultSet rs;

     rs = stmt.executeQuery("SELECT Artist_Name FROM mp3_files WHERE Bit_Rate = 128");
     while (rs.next()) {

         returnedName = rs.getString("Artist_Name");
         System.out.println("Artist Name is: " + returnedName);
         // System.out.println("In Database");
         // System.out.println(returnedData);
         // TODO put information into item here
         
     }
}
    /**
     * Connects to mysql database and runs specific query.
     * @param args
     */

try{
            
            // Two Following prints are verification data

            // System.out.println("URL: " +url);

            // System.out.println("Connection: " +conn);

            // System.out.println("CONNECTED TO DATABASE");
         

            // System.out.println("CONNECTION TERMINATED");
        } catch (Exception e) {

            System.err.println("Got an Exception");

            System.err.println(e.getMessage());

        }
        }
    }
}
