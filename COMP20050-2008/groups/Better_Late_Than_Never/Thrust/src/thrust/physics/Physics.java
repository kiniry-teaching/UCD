package thrust.physics;
/*
 * Taking a look at some of the physics stuff..
 * @author: nm
 * @date: 22-04-08
 */
public class Physics implements PhysicsInterface {
  /** The gravitational constant. */
  public static final double the_grav_constant = 9.8;
  /** Current acceleration. */
  private double my_acceleration;
  /** Current mass. */
  private double my_mass;
  /** Current momentum. */
  private double my_momentum;
  /** Current orientation (radians). */
  private double my_orientation;
  /** Current x coordinate of entity. */
  private double my_xposition;
  /** Current y coordinate of entity. */
  private double my_yposition;
  /** Current velocity. */
  private double my_velocity;
  /** Because 2 is a magic number..*/
  private final int my_magicnumber = 2;



  public double[] acceleration() {
	  double[] accel = new double[2];
	  accel[0] = my_acceleration;
	  accel[1] = my_velocity
	  return accel[];
  }

  public double gravitational_constant() {
    // Doesn't change or need to be private, so public final? - confirm

    return the_grav_constant;
  }

  public double mass() {

    return my_mass;
  }

  public double momentum() {
    // p = m * v
    my_momentum = my_mass * my_velocity;
    return my_momentum;
  }

  public double orientation() {
    // TODO Auto-generated method stub
    return my_orientation;
  }

  public double[] position() {
    final double[] position = new double[my_magicnumber];
    position[0] = my_xposition;
    position[1] = my_yposition;

    return position();
  }

  public void simulate(final double some_seconds) {
    // TODO Auto-generated method stub

  }

  public double[] velocity() {
    // Speed in a given direction (orientation)
    final double[] velocity = new double[my_magicnumber];
    velocity[0] = my_velocity;
    velocity[1] = my_orientation;

    return velocity();
  }

}
