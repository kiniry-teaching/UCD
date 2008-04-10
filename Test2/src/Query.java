import java.awt.List;
import java.io.IOException;
import java.util.ArrayList;
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

    private class MusicItem {
// TODO LORCAN -I'm a little unsure how to implenment this
        public List extractinfo() throws IOException {
            Statement stmt = conn.createStatement();

            ResultSet rs;

            try{
                rs = stmt.executeQuery("SELECT Artist_Name FROM mp3_files WHERE Bit_Rate = 128");
            
            List allItems = new List();
            while (rs.next()) {

                returnedName = rs.getString("Artist_Name");
                System.out.println("Artist Name is: " + returnedName);
                // System.out.println("In Database");
                MusicItem item = new MusicItem();
                // System.out.println(returnedData);
                // TODO put information into item here
                allItems.add(returnedName);
            }
            
            } catch (IOException e1) {
                System.out.println("there was an IO error");
            }

        }
         
            return allItems;
        }


    /**
     * Connects to mysql database and runs specific query.
     * 
     * @param args
     */
    public static void main(final String args[]) {

        try {

            Query q = new Query();
            List items = q.extractinfo();
            //TODO LORCAN - we're unsure about the error that is coming up with extractinfo()
            q.close();
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


    private void close() {
        // TODO Auto-generated method stub
        
    }

    public static String getReturnedName() {
        return returnedName;
    }

    public static void setReturnedName(String returnedName) {
        Query.returnedName = returnedName;
    }

    public Connection getConn() {
        return conn;
    }

    public void setConn(Connection conn) {
        this.conn = conn;
    }
}
