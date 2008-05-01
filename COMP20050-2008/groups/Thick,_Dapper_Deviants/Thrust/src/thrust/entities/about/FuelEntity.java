package thrust.entities.about;

public class FuelEntity implements Fuelable {
  
  public int fuel(){
  {
    if (fuel > 0 && fuel < maximum_fuel){
      return fuel;
    }
    else if (fuel > maximum_fuel){
      return maximum_fuel;
    }
    else if(fuel < 0){
      return  fuel = 0;
     }
  }
  
  }

  public void change_fuel_content(int the_fuel_change) {
    // TODO Auto-generated method stub
    
  }

  public int fuel_mass() {
    // TODO Auto-generated method stub
    return 0;
  }

  public void set_fuel_content(int the_fuel_content) {
    // TODO Auto-generated method stub
    
  }
  

}
