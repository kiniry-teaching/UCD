package ie.ucd.music.comparison.Database;

import java.util.regex.Matcher;
import java.util.regex.Pattern;



/**

 *This program accesses a database

 *and extract information about mp3 files

 *in the form of ID3 tag information.

 *The extracted tags are then compared

 *to tags from another mp3 file and if

 *the two tags are found similar further

 *ID3 tag information is checked. If

 *enough is found similar between two

 *files then they are linked together in

 *a list and passed to the next stage of

 *the software.

 * @return List Of Strings

 */

public class CompareString {

    /**

     * A string is taken as an argument And Through a series of pattern/ matches

     * the string is cleaned to a form where any preceding 'the' or 'a' is

     * removed and any underscores etc. between words in a string are also

     * removed. the clean form of the string is then returned

     * @param name = String

     * @return String

     */



    public String setCompareString(final String name) {

        String setString = name;

        StringBuffer finalString = new StringBuffer();

        Pattern firstPattern = Pattern

                .compile("(?i)([a-z]|[0-9])+(\\p{Punct}|\\p{Blank})");

        Pattern fifthPattern = Pattern.compile("(?i)[a-z]+");

        Matcher firstMatch = firstPattern.matcher(setString);

        if (firstMatch.find()) {

            setString = setString.substring(firstMatch.start());

            String start = firstMatch.group(0);

            Pattern secondPattern = Pattern

                    .compile("((?i)a(\\p{Punct}|\\p{Blank}))"

                            + "|((?i)the(\\p{Punct}|\\p{Blank}))");

            Matcher secondMatch = secondPattern.matcher(start);

            Matcher thirdMatch = secondPattern.matcher(setString);

            if ((secondMatch.find()) && (thirdMatch.find())) {

                setString = setString.substring(thirdMatch.end());

            }

        }

        Matcher fifthMatch = fifthPattern.matcher(setString);

        while (fifthMatch.find()) {

            fifthMatch.appendReplacement(finalString, fifthMatch.group()

                    .toLowerCase());

        }

        return finalString.toString();

    }   /**

     *This method returns a boolean.

     *Two Strings are entered as arguments

     *each word is then extracted from the

     *first string and each in turn is set

     *as a pattern and compared to the second

     *string. 3 double values- AllWords, SimWords

     *and CorrectPer are used to  calculate the

     *percentage of words common from the first

     *string in the second string. if this is

     *above 80% the two strings are determined

     *to be similar

     * @param one = String

     * @param two = String

     * @return Boolean

     */

    public boolean compareTwoStrings(

            final String one, final String two) {

        String temp;

        double allWords = 0.0;

        double simWords = 0.0;

        Pattern csPat1 = Pattern.compile("[a-z]+");

        Matcher csMat1 = csPat1.matcher(one);

        while (csMat1.find()) {

            temp = csMat1.group(0);

            allWords = allWords + 1;

            Pattern csPat2 = Pattern.compile(temp);

            Matcher csMat2 = csPat2.matcher(two);

            if (csMat2.find()) {

                simWords = simWords + 1;

            }

        }

        double correctPer = allWords / simWords;

        return (correctPer <= 1.25);

    }

   

}

