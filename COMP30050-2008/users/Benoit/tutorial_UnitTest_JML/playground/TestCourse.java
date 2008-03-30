package playground;

import junit.framework.*;

public class TestCourse extends TestCase{

     private Course c;
       
     public TestCourse(String name) {
       super(name);
     }
   
     protected void setUp() { 
       c = new Course();
       c.setName("St. Andrews");
       int[] par = {4,4,4,4,5,4,4,3,4,4,3,4,4,5,4,4,4,4};
       c.setPar(par);         
     }
   
     public void testGetNumberOfHoles(){
        assertEquals(18, c.getNumberOfHoles());
     }
     
     public void testDefaultCourse(){
        Course def = new Course();
        assertEquals(0, def.getNumberOfHoles());
     }
     
     public void testParUpToHole() {
       assertEquals(0, c.parUpToHole(0));
       assertEquals(8, c.parUpToHole(2));
       assertEquals(72, c.parUpToHole(18));
     }
       

   
}
