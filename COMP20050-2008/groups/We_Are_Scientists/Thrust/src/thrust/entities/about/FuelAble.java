   package thrust.entities.about;
   /**
    * @author simon markey 
    * @version 11 April 2008
    */
   public class FuelAble implements Fuelable {
   
     /**The integer value that is the fuel*/
     float Fuel;
     
    /**maximum fuel availible.*/
    final float MaxFuel = Float.POSITIVE_INFINITY;
  
    public FuelAble(final float initialFuel) {
      Fuel = initialFuel;
    }
    /**
     * @return How much fuel do you contain?
     */
    //@ ensures 0 <= \result;
    //@ ensures \result <= maximum_fuel();
    public /*@ pure @*/ float fuel() {
      return Fuel;
    }
  
    /**
     * @return How much fuel can you contain?
     */
    //@ ensures 0 <= \result;
    public /*@ pure @*/ float maximum_fuel() {
  
      return MaxFuel;
    }
  
    /**
     * @param the_fuel_content This many units is your fuel content.
     */
    //@ requires 0 <= the_fuel_content & the_fuel_content <= maximum_fuel();
    //@ ensures fuel() == the_fuel_content;
    public void set_fuel_content(final float the_fuel_content) {
      
      if(the_fuel_content >= 0 && the_fuel_content <= maximum_fuel()) {
        Fuel = the_fuel_content;
      }
    }
    /**
     * @param fuel_difference Change your fuel content by this many units.
     */
    /*@ ensures (\old(fuel() + the_fuel_change < 0) ?
        @            (fuel() == 0) :
        @          (\old(maximum_fuel() < (fuel() + the_fuel_change)) ?
        @             (fuel() == maximum_fuel()) :
        @           fuel() == \old(fuel() + the_fuel_change)));
        @*/
    public void change_fuel_content(final float fuel_difference) {
  
      if (Fuel + fuel_difference < 0) {
        Fuel = 0;
      }
  
      if (Fuel + fuel_difference > MaxFuel) {
        Fuel = MaxFuel;
      }
  
      Fuel = Fuel + fuel_difference;
  
      //@ invariant (* Fuel content is always non-negative and finite. *);
      //@ invariant 0 <= fuel();
    }
    public float fuel_mass() {
      if(Fuel<0)
      return fuel()*-1;
      else
      {
        return Fuel*1;
      }
  
    }
  
 }