package playground;

public class Round {

     private String player; // name of player
     private Course course; // name of the course
     private int[] score; // scores for each hole
     private int currentHole = 0; // the last played hole
     
     /*
     * Set the name of the player
     */
     public void setPlayer(String name) {
       player = name;
     }
     
     /*
     * Set the course
     */
     public void setCourse(Course c) {
       course = c;
       score = new int[course.getNumberOfHoles()];
     }
     
     /*
     * Set the number of strokes for the current hole
     */
     public void newScore(int s) {
       score[currentHole] = s;
       currentHole++;
     }
     
     /*
     * Get the number of strokes used so far
     */
     public int currentStrokes() {
       int sum = 0;
       for (int i = 0; i < currentHole; i++) { 
         sum += score[i];
       }
       return sum;
     }
     
     /*
     * Get the current score relative 
     *to the par of the course
     */
     public int currentScore() {
       return currentStrokes() - 
         course.parUpToHole(currentHole);
     }
   
}
