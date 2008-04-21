package thrust.physics;

/**
 * First implementation of Physics class.
 * Stores current values of parameters of Entity's state.
 * @author Magdalena Zieniewicz (mazienie@gmail.com)
 * @version 14 April 2008
 * */

public class Physics1 implements PhysicsInterface {

  /** Value of the gravitational constant. */
  public static final int THE_GRAV_CONST = 5;
  /** Length of an array storing vector parameter. */
  private final int my_array_length_2 = 2;
  /** Current mass of the Entity.*/
  private double my_mass;
  /** Current speed of the Entity.  */
  private double my_speed;
  /** Value of current acceleration of the Entity.*/
  private double my_acceleration;
  /** Orientation of the Entity. */
  private double my_orientation;
  /** Horizontal position of the Entity.  */
  private double my_position_x;
  /** Vertical position of the Entity.  */
  private double my_position_y;
  /** Time for stimulation  */
  private double my_time;

  public Physics1(PhysicsInterface phi) {
    
    my_mass = phi.mass();
    my_speed = (phi.velocity())[0];
    my_acceleration = (phi.acceleration())[0];
    my_orientation = phi.orientation();
    my_position_x = (phi.position())[0];;
    my_position_y = (phi.position())[1];;

  }

  public int getArrayLength() {
    return my_array_length_2;
  }


  public double[] acceleration() {
    final double[] acceleration = new double[getArrayLength()];
    acceleration[0] = my_acceleration;
    acceleration[1] = my_orientation;
    return acceleration;
  }

  public double gravitational_constant() {
    return THE_GRAV_CONST;
  }

  public double mass() {
    return my_mass;
  }

  public double momentum() {
    return my_mass * my_speed;
  }

  public double orientation() {
    return my_orientation;
  }

  public double[] position() {
    final double[] position = new double[getArrayLength()];
    position[0] = my_position_x;
    position[1] = my_position_y;
    return position;
  }

  public double[] velocity() {
    final double [] velocity = new double[getArrayLength()];
    velocity[0] = my_speed;
    velocity[1] = my_orientation;
    return velocity;
  }
  
  public void simulate(double time){
    time = my_time;
  }

}
