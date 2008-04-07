package thrust.physics;

public abstract class AbstractPhysics implements Physics {
  
  final double G = -9.8;
  double mass;
  double speed;
  double rate_of_speed;
  double orientation;
  double x;
  double y;

  public double[] acceleration() {
    double[] acceleration = {speed, rate_of_speed};
    return acceleration;
  }

  public double gravitational_constant() {
    return G;
  }

  public double mass() {
    return mass;
  }

  public double momentum() {
    return mass*speed;
  }

  public double orientation() {
    return orientation;
  }

  public double[] position() {
    double[] position = {x, y};
    return position;
  }

  public double[] velocity() {
    double[] velocity = {speed, orientation};
    return velocity;
  }

}
