package ui;
import selfCheckOut2.BarCode;
//ItemQuery.java class designed to create a new product object,
 	//create query based on a barcode, return all necessary data,
 	//eliminates need for two seperate classes, replaces Product.java and
 	//Query.java
 	
 	import java.sql.*;
 	
 	public class Item {
 	        String name;
 	        int price;
	        int minweight;
 	        int weight;
 	        int maxweight;
 	        String soundfile;
 	        String imagefile;
 	        String allergy;
 	        int primeitem;
 	        BarCode barcode;
 	       
 	
 	        public Item (BarCode bc){
 	        //
 	       
 	       
 	        //public ItemQuery (long barcode) {
 	                try{
 	                        Class.forName("com.mysql.jdbc.Driver").newInstance();
 	                       
 	                        //String url  = "jdbc:mysql://sql104.hostwq.net:3306/hq_1793448_SelfCheckout";
 	                        //String url  = "jdbc:mysql://169.254.117.255:3306/SelfCheckout";
 	                        String url  = "jdbc:mysql://localhost:3306/SelfCheckout";
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
 	                        rs = stmt.executeQuery("SELECT Name,Price,MinWeight,Weight,MaxWeight"
	                                        +",SoundFileLoc,ImageFileLoc,Allergy,PrimeItem FROM Items WHERE Barcode = "+bc.getBarCodeLong() +"");
 	                       
 	                        while ( rs.next() ) {
 	                                name = rs.getString("Name");
 	                                price = rs.getInt("Price");
 	                                minweight = rs.getInt("MinWeight");
 	                                weight = rs.getInt("Weight");
 	                                maxweight = rs.getInt("MaxWeight");
 	                                soundfile = rs.getString("SoundFileLoc");
 	                                imagefile = rs.getString("ImageFileLoc");
 	                                allergy = rs.getString("Allergy");
 	                                primeitem = rs.getInt("PrimeItem");
 	                                this.barcode = bc;
 	                               
 	                               
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