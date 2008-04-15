/**
 * class implemented by Daire O'Doherty 06535691 14/4/08
 */

package thrust.entities.about;
/**
 * @author Daire O'Doherty 06535691
 * @version 14 April 2008
 */

public abstract class Fueling implements Fuelable {
  /**
   * @return How much fuel do you contain?
   */
  
    public int myFuel;
    
    public int myMaxi = 100;
  
  //@ ensures 0 <= \result;
  //@ ensures \result <= maximum_fuel();
  /*@ pure @*/ 
  public int fuel() {
    return myFuel;
  }
  /**
   * @return How much fuel can you contain?
   */
  //@ ensures 0 <= \result;
  /*@ pure @*/ 
public final int maximum_fuel() {
  if (myMaxi >= 0){
    return myMaxi;
  }
}

  /**
   * @param the_fuel_content This many units is your fuel content.
   */
  //@ requires 0 <= the_fuel_content & the_fuel_content <= maximum_fuel();
  //@ ensures fuel() == the_fuel_content;
  public final void set_fuel_content(final int the_fuel_content) {
    if(the_fuel_content >= 0 && the_fuel_content <= myMaxi){
    myFuel = the_fuel_content;
    }
    }
  


  /*@ ensures (\old(fuel() + the_fuel_change < 0) ?
    @            (fuel() == 0) :
    @          (\old(maximum_fuel() < (fuel() + the_fuel_change)) ?
    @             (fuel() == maximum_fuel()) :
    @           fuel() == \old(fuel() + the_fuel_change)));
    @*/
  /**
   * @param the_fuel_change Change your fuel content by this many units.
   */
  public final void change_fuel_content(final int the_fuel_change) {
    if (fuel() + the_fuel_change < 0) {
      myFuel = 0;
    }
    else if (maximum_fuel() < (fuel() + the_fuel_change)) {
      myFuel = maximum_fuel();
    }
    else {
      myFuel = fuel() + the_fuel_change;
    }
  }

  //@ invariant (* Fuel content is always non-negative and finite. *);
  //@ invariant 0 <= fuel();
  
  
 
  
  }
  