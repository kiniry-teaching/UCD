package ie.ucd.music.comparison.Database;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.Statement;

public class Query {
    static String returnedName = "";
    static int returnedValue = 0;

    public String getInfo(String item, String lib, int ident) {

        try {

            Class.forName("com.mysql.jdbc.Driver").newInstance();

            String url = "jdbc:mysql://localhost:3306/Music";

            Connection conn = DriverManager.getConnection(url, "root", "");

            // Two Following prints are verification data
            // System.out.println("URL: " +url);
            // System.out.println("Connection: " +conn);
            // System.out.println("CONNECTED TO DATABASE");
            // System.out.println("");

            Statement stmt = conn.createStatement();
            ResultSet rs1;
            rs1 = stmt.executeQuery("SELECT " + item + " FROM " + lib
                    + " WHERE Id = " + ident);

            while (rs1.next()) {

                returnedName = rs1.getString(item);

                // System.out.println("In Database");
                // System.out.println(returnedData);
            }

            conn.close();

            // System.out.println("CONNECTION TERMINATED");
        }

        catch (Exception e) {

            // System.err.println("Got an Exception");
            // System.err.println(e.getMessage());

        }
        return returnedName;
    }

    /**
     * Connects to the database and runs a query that returns the bit rate.
     * 
     * @param lib =
     *                the table name
     * @param ident =
     *                an iterator
     * @return int
     */
    public int getBitRate(final String lib, final int ident) {
        String temp = "";
        try {

            Class.forName("com.mysql.jdbc.Driver").newInstance();

            String url = "jdbc:mysql://localhost:3306/Music";

            Connection conn = DriverManager.getConnection(url, "root", "");

            // Two Following prints are verification data
            // System.out.println("URL: " +url);
            // System.out.println("Connection: " +conn);
            // System.out.println("CONNECTED TO DATABASE");
            // System.out.println("");
            Statement stmt = conn.createStatement();
            ResultSet rs1;
            rs1 = stmt.executeQuery("SELECT Bit_Rate FROM " + lib
                    + " WHERE Id = " + ident);

            while (rs1.next()) {

                temp = rs1.getString("Bit_Rate");
                returnedValue = Integer.parseInt(temp);
                // System.out.println("In Database");
                // System.out.println(returnedData);
            }

            conn.close();
            returnedValue = 0;

            // System.out.println("CONNECTION TERMINATED");

        }

        catch (Exception e) {

            // System.err.println("Got an Exception");
            // System.err.println(e.getMessage());

        }
        return returnedValue;
    }

    public static void main(String[] args) {
        Query qart = new Query();
        MusicItem track1 = new MusicItem();
        MusicItem track2 = new MusicItem();
        CompareString compS = new CompareString();
        for (int i = 1; i <= 4; i++) {
            String artist1 = qart.getInfo("Artist_Name", "Audio_Files", i);
            String song1 = qart.getInfo("Track_Title", "Audio_Files", i);
            int bitrate1 = qart.getBitRate("Audio_Files", i);

            for (int j = 1; j <= 3; j++) {
                String artist2 = qart.getInfo("Artist_Name", "Audio_Info", j);
                String song2 = qart.getInfo("Track_Title", "Audio_Info", j);
                int bitrate2 = qart.getBitRate("Audio_Info", j);
                String clean1 = compS.setCompareString(artist1);
                String clean2 = compS.setCompareString(artist2);
                if ((compS.compareTwoStrings(clean1, clean2))
                        && (compS.compareTwoStrings(clean2, clean1))) {
                    clean1 = compS.setCompareString(song1);
                    clean2 = compS.setCompareString(song2);
                    if ((compS.compareTwoStrings(clean1, clean2))
                            && (compS.compareTwoStrings(clean2, clean1))) {
                        if (bitrate2 > bitrate1) {
                            System.out
                                    .println("These two tracks were found similar and(higher): "
                                            + artist2 + " " + song2);
                            System.out.println("(lower)" + artist1 + " "
                                    + song1);
                        } else {
                            System.out
                                    .println("These two tracks were found similar and(higher): "
                                            + artist1 + " " + song1);
                            System.out.println("(lower)" + artist2 + " "
                                    + song2);
                        }
                    }
                }

            }
        }
    }
}
