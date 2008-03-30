package playground;

public class Course {

   private String name; // name of course
   private int[] par; // the par for each hole 
   
   /*
   * Set the name of the course
   */
   public void setName(String name) {
     this.name = name;
   }
   
   /*
   * Set the par for the course
   */
   public void setPar(int[] par) {
     this.par = par;
   }

   /*
   * Get the number of holes for the course
   */
   public int getNumberOfHoles() {
     return par.length;
   }
  
   /*
   * Return the par for a given hole
   */
   public int parForHole(int hole) {
     return par[hole-1];
   }  
   
   /*
   * Return the par from hole 1 and up to a given hole
   */
   public int parUpToHole(int hole) {
     int sum = 0;
     for (int i = 0; i < hole; i++) { 
       sum += par[i];
     }
     return sum;
   }
   
}
