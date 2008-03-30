package playground;

import junit.framework.*;

public class TestRound extends TestCase { 
  private Course c;
  private Round tb,tw;
    
  public TestRound(String name) {
    super(name);
  }

  protected void setUp() { 
    c = new Course();
    c.setName("St. Andrews");
    int[] par = {4,4,4,4,5,4,4,3,4,4,3,4,4,5,4,4,4,4};
    c.setPar(par); 
    tb = new Round();
    tb.setPlayer("Thomas Bjorn");
    tb.setCourse(c);
    tw = new Round();
    tw.setPlayer("Tiger Woods");
    tw.setCourse(c); 
  }

  public static Test suite() { 
     TestSuite suite= new TestSuite(); 
     suite.addTest(new TestRound("testTiger")); 
     suite.addTest(new TestRound("testThomas"));
     return suite;
   }
  
  public static void main(String args[]) {
    junit.textui.TestRunner.run(suite());
  }

  public void testTiger() {
    // Test that beginning score is zero
    assertEquals(0, tw.currentStrokes());
    // Player gets a "par" 
    tw.newScore(4);
    assertEquals(4, tw.currentStrokes());
    assertEquals(0, tw.currentScore());
    // Player gets a "birdie" 
    tw.newScore(3);
    assertEquals(7, tw.currentStrokes());
    assertEquals(-1, tw.currentScore());
  }
    
  public void testThomas() {
    // Player gets a "bogey" 
    tb.newScore(5);
    assertEquals(5, tb.currentStrokes());
    assertEquals(1, tb.currentScore());
    // Player gets an "eagle" 
    tb.newScore(2);
    assertEquals(7, tb.currentStrokes());
    assertEquals(-1, tb.currentScore());
  }    
}