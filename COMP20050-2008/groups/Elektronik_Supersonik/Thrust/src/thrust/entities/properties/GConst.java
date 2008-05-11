package thrust.entities.properties;
/**
 * The 'magic number' eliminator.
 * @author Elektronik Supersonik (.@.)
 * @version 05 May 2008
 */
public class GConst {

  /**
   * Screen width.
   */
  public static final int SCR_W = 800;
  /**
   * Screen height.
   */
  public static final int SCR_H = 600;
  /**
   * Frame width.
   */
  public static final int FRM_W = 1000;
  /**
   * Frame height.
   */
  public static final int FRM_H = 635;
  /**
   * Ship diameter.
   */
  public static final int SHIP_D = 30;
  /**
   * Fuel pod diameter.
   */
  public static final int FUEL_D = 20;
  /**
   * Sphere diameter.
   */
  public static final int SPHERE_D = 30;
  /**
   * Factory size.
   */
  public static final int FACT_D = 60;
  /**
   * Factory x coordinate.
   */
  public static final int FACT_X = 450;
  /**
   * Factory Y coordinate.
   */
  public static final int FACT_Y = 540;
  /**
   * Ship x coordinate.
   */
  public static final int SHP_STRTX = 450;
  /**
   * Ship y coordinate.
   */
  public static final int SHP_STRTY = 50;
  /**
   * Score gained for destroying turret.
   */
  public static final int TRT_SCORE = 750;
  /**
   * Turret x coordinate.
   */
  public static final int TRT_X = 280;
  /**
   * Turret y coordinate.
   */
  public static final int TRT_Y = 580;
  /**
   * Turret width.
   */
  public static final int TRT_W = 60;
  /**
   * Turret height.
   */
  public static final int TRT_H = 20;
  /**
   * Sphere x coordinate.
   */
  public static final int SPH_X = 400;
  /**
   * Sphere y coordinate.
   */
  public static final int SPH_Y = 565;
  /**
   * Sphere mass.
   */
  public static final double SPH_MASS = 10000.0;
  /**
   * Pod dimensions.
   */
  public static final int POD_D = 20;
  /**
   * Pod x coordinate.
   */
  public static final int POD_X = 720;
  /**
   * Pod y coordinate.
   */
  public static final int POD_Y = 580;
  /**
   * The score for rescuing the goal sphere.
   */
  public static final int WIN_SCORE = 3000;
  /**
   * The distance at which the turret starts firing.
   */
  public static final int TRT_FR_DIST = 250;
  /**
   * The bullet velocity.
   */
  public static final int BUL_VEL = 100;
  /**
   * Bullet dimension.
   */
  public static final int BUL_D = 2;
  /**
   * The number of milliseconds you have to escape after factory explosion.
   */
  public static final int ESC_TIME = 20000;
  /**
   * The acceleration gained from thrusting.
   */
  public static final double ACC_GAIN = 5;
  /**
   * The time in milliseconds turrets are disabled after factory hit.
   */
  public static final int DIS_TIME = 4000;
  public GConst() {
    assert false;
  }
}
