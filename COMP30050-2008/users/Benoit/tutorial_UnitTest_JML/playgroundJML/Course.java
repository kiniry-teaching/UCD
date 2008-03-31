package playgroundJML;

public class Course {

   private String name; // name of course
   private int[] par; // the par for each hole 
   
   /*
    * Class Constructor
    */
   Course(String n, int[] p){
      name = n;
      par = p;
   }
   
   /*
   * Set the name of the course
   */
   /*@
   @ assignable name;
   @ ensures name.equals(n);
   @*/
   public void setName(String n) {
     this.name = n;
   }
   
   /*
   * Set the par for the course
   */
   /*@
   @ assignable par;
   @*/
   public void setPar(/*@ non_null @*/ int[] par) {
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
   /*@
   @ requires 0 < hole && hole <= par.length;
   @ ensures 0 < \result;
   @*/
   public /*@ pure @*/ int parUpToHole(int hole) {
     int sum = 0;
     for (int i = 0; i < hole; i++) { 
        //@ assert 0 <= i && i < hole;
       sum += parForHole(i+1);
     }
     return sum;
   }
   
   
   public static void main(String[] arg){
      Course c = new Course();
      c.setName("St. Andrews");
      int[] par = {4,4,4,4,5,4,4,3,4,4,3,4,4,5,4,4,4,4};
      c.setPar(par);
      
      System.out.println(0 == c.parUpToHole(0));
      System.out.println(8 == c.parUpToHole(2));
      System.out.println(72 == c.parUpToHole(18));
   }
   
}
