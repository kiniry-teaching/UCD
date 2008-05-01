package thrust.entities.about;

public class FuelEntity implements Fuelable {


  /*
   * @return The current fuel of the object
   */
  
  private int my_fuel;

  int maximum_fuel = 1000;

  int fuel_weight = 1;

  public int check_fuel(){
    {
      if (fuel > 0 && fuel < maximum_fuel) {
        return fuel;
      }
      else if (fuel >= maximum_fuel) {
        return maximum_fuel;
      }
      else if (fuel == 0) {
        return fuel;
      }
    }
  }

  public void change_fuel_content(int the_fuel_change) {
    // TODO Auto-generated method stub
  }

  public int fuel_mass() {
    // TODO Auto-generated method stub
    return fuel * fuel_weight;
  }

  public void set_fuel_content(int the_fuel_content) {
    // TODO Auto-generated method stub
  }
  public int max_fuel() {
    // TODO Auto-generated method stub
    return maximum_fuel;
  }


}
