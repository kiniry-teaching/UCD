package thrust.physics;
/*
 * Taking a look at some of the physics stuff..
 * Author: nm
 * Date: 22-04-08
 */
public class Physics implements PhysicsInterface {
  /* The gravitational constant */
  public final double gravConstant;
  /* Current acceleration */
  private double myAcceleration;
  /* Current mass */
  private double myMass;
  /* Current momentum */
  private double myMomentum;
  /* Current orientation (radians) */
  private double myOrientation;
  /* Current x coordinate of entity */
  private double myXPosition;
  /* Current y coordinate of entity */
  private double myYPosition;
  /* Current velocity */
  private double my_velocity;



  public double[] acceleration() {
   /* a = ((v1-v0)/t) ... */

    double test = myAcceleration;
    return acceleration();
  }

  public double gravitational_constant() {
    // Doesn't change or need to be private, so public final? - confirm
    
    return gravConstant;
  }

  public double mass() {
    
    return myMass;
  }

  public double momentum() {
    // p = m * v
    myMomentum = myMass * myVelocity;
    return myMomentum;
  }

  public double orientation() {
    // TODO Auto-generated method stub
    return myOrientation;
  }

  public double[] position() {
    final double[] position = new double[2];
    position[0] = myXPosition;
    position[1] = myYPosition;

    return position();
  }

  public void simulate(double some_seconds) {
    // TODO Auto-generated method stub

  }

  public double[] velocity() {
    // Speed in a given direction (orientation)
    double[] velocity = new double[2];
    velocity[0] = myVelocity;
    velocity[1] = myOrientation;

    return velocity();
  }

}
