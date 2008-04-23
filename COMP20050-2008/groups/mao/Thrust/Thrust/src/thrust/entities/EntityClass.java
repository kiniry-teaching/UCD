package thrust.entities;

import java.awt.Color;
import java.awt.Shape;

public class EntityClass extends Entity {
  
  
  private Shape shape;
  private byte state;
  private Color color;

  public  String shape_name(){
    return shape.toString();
  }

  /**
   * @return What shape are you?
   */
  public  Shape shape(){
    return shape;
  }
    
  /**
   * This is your shape.
   * @param the_shape the shape of this Entity.
   */
  public void shape(Shape the_shape){
    shape = the_shape;
  }

  /**
   * @return What is your physical state?
   * @note State is encoded by a non-negative number of "hit points".
   */
  //@ ensures 0 <= \result;
  public byte state(){
    return state;
  }

  /**
   * This is your physical state.
   * @param the_state the state.
   */
  //@ requires 0 <= the_state;
  //@ ensures state() == the_state;
  public void state(byte the_state){
    state = the_state;
  }

  /**
   * Render yourself.
   */
  public void render(){
    
}
  /**
   * @return What color are you?
   */
  //@ ensures \result == _the_color;
  public /*@ pure @*/ Color color(){
    return color;
  }

  /**
   * This is your color.
   * @the_color the new color.
   */
  //@ ensures color() == the_color;
  public void color(Color the_color){
    color = the_color;
  }
  
  
}
