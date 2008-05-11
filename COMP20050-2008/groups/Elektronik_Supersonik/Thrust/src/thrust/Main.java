/*
 * A re-implementation of the classic C=64 game 'Thrust'. @author "Joe Kiniry
 * (kiniry@acm.org)" @module "COMP 20050, COMP 30050" @creation_date "March
 * 2007" @last_updated_date "April 2008" @keywords "C=64", "Thrust", "game"
 */

package thrust;

import java.awt.BorderLayout;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Shape;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.geom.Ellipse2D;
import java.awt.geom.Line2D;
import java.awt.geom.Point2D;
import java.awt.geom.Rectangle2D;
import java.awt.geom.RectangularShape;
import java.awt.Color;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

// import thrust.audio.Music;
import thrust.entities.DynamicEntity;
import thrust.entities.Entity;
import thrust.entities.StaticEntity;
import thrust.entities.in_game.Factory;
import thrust.entities.in_game.Bullet;
import thrust.entities.in_game.FuelPod;
import thrust.entities.in_game.GameState;
import thrust.entities.in_game.GoalSphere;
import thrust.entities.in_game.GunTurret;
import thrust.entities.in_game.Spaceship;
import thrust.entities.properties.GConst;
import thrust.input.InputHandler;

/**
 * Simulating all of the entities in the game to realize the game.
 * @author Elektronik Supersonik (.@.)
 * @version 23 April 2008
 */
public final class Main {

  /**
   * The information screen.
   */
  private static JTextArea infoScreen;
  /**
   * The main frame for the game screen.
   */
  private static JFrame mainFrame;
  /**
   * The text-display field in the main frame.
   */
  private static JTextArea console;
  /**
   * The scroll bar for the text area.
   */
  private static JScrollPane scroll;
  /**
   * The key listener for the game.
   */
  private static MainKeys inputListener;
  /**
   * The game state.
   */
  private static GameState game;
  /**
   * The input handler for the game.
   */
  private static InputHandler input;
  /**
   * The rectangle that describes valid movement(map bounds).
   */
  private static Rectangle2D.Double mapBounds;
  /**
   * The spaceship entity.
   */
  private static Spaceship playerShip;
  /**
   * The factory entity.
   */
  private static Factory theFactory;
  /**
   * The turret entity.
   */
  private static GunTurret theTurret;
  /**
   * The goal sphere entity.
   */
  private static GoalSphere theSphere;
  /**
   * The fuel pod entity.
   */
  private static FuelPod theFuelPod;
  /**
   * The component responsible for drawing the the entities.
   */
  private static GameDraw drawComponent;
  /**
   * The maximum number of player-launched bullets that can be on screen
   * at one given time.
   */
  private static final int NUM_BULLETS = 4;
  /**
   * The number of bullets currently on screen.
   */
  private static int bulletCount;
  /**
   * The list of renderable entity shapes.
   */
  private static List renderable;
  /**
   * Started boolean.
   */
  private static boolean started;
  /**
   * The list of entities involved in the game.
   */
  private static List entities;
  /**
   * The list of player-launched bullets in the game.
   */
  private static List playerBullets;
  /**
   * The state the game is in (menu, gameplay, etc.).
   */
  private static byte my_state;
  /**
   * Tells if the spaceship has the shields active.
   */
  private static boolean shieldOn;
  /**
   * Tells if the game is over.
   */
  private static boolean over;
  /**
   * The number of turret bullets.
   */
  private static int tur_bullets;
  /**
   * The turret bullet list.
   */
  private static List turBullets;
  /**
   * The deadline for escaping the planet after the factory destruction.
   */
  private static long deadline = -1;
  /**
   * Tells if the turrets are disabled.
   */
  private static long disableTimer = -1;
  /**
   * This class cannot be constructed.
   */
  private Main() {
    assert false; // @ assert false;
  }

  /**
   * Run the game.
   * @param the_args The command-line arguments are ignored.
   */
  public static void main(final String[] the_args) {
    game = new GameState();
    my_state = GameState.MENU_STATE;
    createWelcomeScreen();
    displayHighScores();
    initializeEntities();
    while (true) {
      shieldOn = false;
      input.process((char) inputListener.lastKeyPressed());
      if (started && !over) {
        cycleEntities();
        drawComponent.updateShapes(renderable);
        checkStatus();
        if (game.lives() < 0) {
          lose();
        }
        displayInfo();
      }
      mainFrame.update(mainFrame.getGraphics());
      sleep();
    }
  }

  private static void lose() {
    over = true;
    createWelcomeScreen();
    console.setText("You lost! Your final score is:" + game.score());
    started = false;
  }

  private static void checkStatus() {
    if (!mapBounds.contains(playerShip.position()[0],
      playerShip.position()[1])) {
      killShip();
    }
    if (playerShip.fuel() <= 0) {
      killShip();
    }
    if(deadline != -1 && System.currentTimeMillis() >= deadline) {
      lose();
    }
    if(disableTimer != -1 && System.currentTimeMillis() >= disableTimer) {
      disableTimer = -1;
    }
    if (playerShip.towed() && playerShip.position()[1] <= GConst.SHIP_D) {
      createWelcomeScreen();
      game.change_score(GConst.WIN_SCORE);
      console.setText("You WIN!!! Your final score: " + game.score());
      over = true;
    }
  }

  private static void killShip() {
    playerShip.position(new double[] {GConst.SHP_STRTX, GConst.SHP_STRTY});
    game.change_lives((byte)-1);
    playerShip.set_fuel_content(Spaceship.INITIAL_FUEL);
    playerShip.acceleration(new double[] {0, 0});
    playerShip.velocity(new double[] {0, 0});
    playerShip.orientation(0);
  }

  private static void displayHighScores() {
    for (int i = 0; i < game.high_scores().length; ++i) {
      console.setText(" " + game.high_score(i).score() + "\n" +
          console.getText());
      for (int j = 0; j < game.high_score(i).initials().length; ++j) {
        console.setText(game.high_score(i).initials()[j] + console.getText());
      }
    }
  }

  public static void createWelcomeScreen() {
    my_state = GameState.MENU_STATE;
    started = false;
    if (mainFrame != null) {
      mainFrame.dispose();
    }
    mainFrame = new JFrame("Thrust");
    mainFrame.setSize(GConst.FRM_W, GConst.FRM_H);
    console = new JTextArea();
    scroll = new JScrollPane(console);
    mainFrame.add(scroll);
    console.setText("Welcome to Thrust");
    console.setFocusable(false);
    console.setEditable(false);
    mainFrame.setVisible(true);
    mainFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    inputListener = new MainKeys();
    mainFrame.addKeyListener(inputListener);
    input = new InputHandler();
  }

  private static void cycleEntities() {
    final int my_dirlen = 25;
    renderable = new ArrayList();
    renderable.add(mapBounds);
    for (int i = 0; i < entities.size(); ++i) {
      processEntity((Entity) entities.get(i), i);
    }
    final Ellipse2D.Double plShape = (Ellipse2D.Double) playerShip.shape();
    final Point2D.Double origin =
        new Point2D.Double(plShape.getCenterX(), plShape.getCenterY());
    final Point2D.Double destination =
        new Point2D.Double((plShape.getCenterX() + my_dirlen *
            Math.sin(Math.toRadians(playerShip.orientation()))),
            (plShape.getCenterY() + my_dirlen * Math.cos(Math
              .toRadians(playerShip.orientation()))));
    final Line2D.Double orientLine = new Line2D.Double(origin, destination);
    renderable.add(orientLine);
    cycleBullets();
    cycleEnemyBullets();
  }

  private static void processEntity(final Entity the_ent, final int the_index) {
    if (!(the_ent instanceof StaticEntity)) {
      simulateDynamic(the_ent);
    }
    renderable.add(((Entity) the_ent).shape());
    checkForDamage(the_ent, the_index);
    if (!(the_ent instanceof Spaceship) && !(the_ent instanceof GoalSphere)) {
      checkCollisions(the_ent);
    }
    if (shieldOn && the_ent instanceof FuelPod) {
      fuelUp(the_ent, the_index);
    }
    if (the_ent instanceof GoalSphere) {
      dealWithSphere(the_ent);
    }
  }

  private static void cycleEnemyBullets() {
    final double my_simulatetime = 0.1;
    for (int i = 0; i < turBullets.size(); ++i) {
      final Bullet cur_ent = (Bullet) turBullets.get(i);
      cur_ent.simulate(my_simulatetime);
      if (!mapBounds.contains(cur_ent.shape().getBounds())) {
        turBullets.remove(i);
        tur_bullets--;
      }
      if (playerShip.shape().contains(cur_ent.shape().getBounds())) {
        killShip();
        turBullets.remove(i);
        tur_bullets--;
      }
      updateShape(cur_ent);
      renderable.add(cur_ent.shape());
    }
  }

  private static void checkForDamage(final Entity the_ent, final int the_ind) {
    if (the_ent instanceof GunTurret) {
      final GunTurret theGun = (GunTurret) the_ent;
      final Random rand = new Random();
      if (checkForHits(the_ent.shape())) {
        entities.remove(the_ind);
        game.change_score(GConst.TRT_SCORE);
      } else {
        final Point2D.Double player = new Point2D.Double(playerShip.
          position()[0], playerShip.position()[1]);
        final Point2D turret = new Point2D.Double(theGun.position()[0],
          theGun.position()[1]);
        if ((player.distance(turret) < GConst.TRT_FR_DIST) && (tur_bullets <
            NUM_BULLETS) && disableTimer == -1) {
          tur_bullets++;
          final int orient = rand.nextInt(170);
          turBullets.add(new Bullet(theGun.position(), 0, new double[] {0, 0},
              0, new double[] {
                GConst.BUL_VEL * Math.sin(Math.toRadians(orient)),
                GConst.BUL_VEL * Math.cos(Math.toRadians(orient))}, "",
              new Rectangle2D.Double(theGun.position()[0],
                  theGun.position()[1], GConst.BUL_D, GConst.BUL_D), (byte) 0));
        }
      }
    }
    if (the_ent instanceof Factory && checkForHits(the_ent.shape())) {
      hitFactory(the_ent, the_ind);
    }
  }

  private static void checkCollisions(final Entity the_ent) {
    if (the_ent.shape().intersects(playerShip.shape().getBounds())) {
      killShip();
    }
    if (theSphere.towed() && the_ent.shape().intersects(theSphere.shape()
      .getBounds())) {
      lose();
    }
  }

  private static void simulateDynamic(final Entity the_ent) {
    final double my_simulatetime = 0.1;
    if (((DynamicEntity)the_ent).state() != 1) {
      ((DynamicEntity) the_ent).simulate(my_simulatetime);
      updateShape((DynamicEntity) the_ent);
    }
  }

  private static void hitFactory(final Entity the_ent, final int the_index) {
    final Factory entf = (Factory)the_ent;
    final int hitScore = 200;
    entf.damage((byte)1);
    if (entf.damage() > 10) {
      entf.chimney().smoking(false);
    }
    if (entf.damage() >= Factory.HEALTH_LIMIT) {
      entities.remove(the_index);
      deadline = System.currentTimeMillis() + GConst.ESC_TIME;
    } else {
      disableTimer = System.currentTimeMillis() + GConst.DIS_TIME;
    }
    game.change_score(hitScore);
  }

  private static void dealWithSphere(final Entity the_ent) {
    final GoalSphere sphereEnt = (GoalSphere) the_ent;
    if (shieldOn) {
      final int pickUpDistance = 90;
      final Point2D.Double player = new Point2D.Double(playerShip
        .position()[0], playerShip.position()[1]);
      final Point2D sphere = new Point2D.Double(sphereEnt.position()[0],
        sphereEnt.position()[1]);
      if (player.distance(sphere) < pickUpDistance) {
        sphereEnt.tow();
        playerShip.tow();
      }
    }
    if (sphereEnt.towed()) {
      sphereEnt.state((byte)0);
    }
  }

  private static void fuelUp(final Entity the_ent, final int the_index) {
    final int my_fuelUp = 4;
    final int fuelUpDistance = 90;
    final FuelPod podEnt = (FuelPod) the_ent;
    final Point2D.Double player = new Point2D.Double(playerShip
      .position()[0], playerShip.position()[1]);
    final Point2D pod = new Point2D.Double(podEnt.position()[0],
      podEnt.position()[1]);
    if (player.distance(pod) < fuelUpDistance) {
      playerShip.set_fuel_content(playerShip.fuel() + my_fuelUp);
      podEnt.set_fuel_content(podEnt.fuel() - my_fuelUp);
      if (podEnt.fuel() <= 0) {
        entities.remove(the_index);
      }
    }
  }

  private static void cycleBullets() {
    final double my_simulatetime = 0.1;
    for (int j = 0; j < playerBullets.size(); ++j) {
      final Bullet bull = (Bullet) playerBullets.get(j);
      if (mapBounds.contains(bull.position()[0], bull
          .position()[1])) {
        ((Bullet)playerBullets.get(j)).simulate(my_simulatetime);
        updateShape((Bullet)playerBullets.get(j));
        renderable.add(((Bullet)playerBullets.get(j)).shape());
      } else {
        playerBullets.remove(j);
        bulletCount--;
      }
    }
  }

  private static boolean checkForHits(final Shape the_shape) {
    boolean ret = false;
    for (int i = 0; i < playerBullets.size(); ++i) {
      final Bullet bull = (Bullet) playerBullets.get(i);
      if (the_shape.contains(bull.position()[0], bull.position()[1])) {
        playerBullets.remove(bull);
        bulletCount--;
        ret = true;
      }
    }
    return ret;
  }

  public static void createGameScreen() {
    if (!over) {
      final JPanel infoPanel = new JPanel();
      infoScreen = new JTextArea();
      infoScreen.setFocusable(false);
      infoPanel.setFocusable(false);
      my_state = GameState.GAMEPLAY_STATE;
      started = true;
      if (mainFrame != null) {
        mainFrame.dispose();
      }
      infoScreen.setFont(new Font("Courier", 0, 14));
      infoPanel.setSize(80, GConst.FRM_H);
      infoPanel.add(infoScreen);
      mapBounds = new Rectangle2D.Double(0, 0, GConst.SCR_W, GConst.SCR_H);
      drawComponent = new GameDraw(renderable);
      mainFrame = new JFrame("Thrust");
      mainFrame.add(infoPanel, BorderLayout.WEST);
      mainFrame.setVisible(true);
      mainFrame.setSize(GConst.FRM_W, GConst.FRM_H);
      mainFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
      mainFrame.add(drawComponent);
      mainFrame.update(mainFrame.getGraphics());
      mainFrame.addKeyListener(inputListener);
    }
  }

  private static void displayInfo() {
    String infoString;
    infoString = "Lives: " + game.lives() + "\nFuel: " + playerShip.fuel() +
      "\nScore: " + game.score();
    if(deadline != -1) {
      infoString = infoString + "\nExplosion in: " +
      ((deadline - System.currentTimeMillis()) / 1000) + "s";
    }
    infoString = "                  \n" + infoString;
    infoScreen.setText(infoString);
  }

  private static void initializeEntities() {
    renderable = new ArrayList();
    entities = new ArrayList();
    playerBullets = new ArrayList();
    turBullets = new ArrayList();
    renderable.add(mapBounds);
    playerShip =
        new Spaceship(new double[] {GConst.SHP_STRTX, GConst.SHP_STRTY}, 0,
            new double[] {0, 0}, Spaceship.EMPTY_MASS + Spaceship.INITIAL_FUEL,
            new double[] {0, 0}, "Triangle", new Ellipse2D.Double(
                GConst.SHP_STRTX, GConst.SHP_STRTY, GConst.SHIP_D,
                GConst.SHIP_D), (byte) 0);
    entities.add(playerShip);
    renderable.add(playerShip.shape());
    theFactory =
        new Factory(new double[] {GConst.FACT_X, GConst.FACT_Y}, 0.0,
            new double[] {0, 0}, 0.0, new double[] {0, 0}, "Rectangle",
            new Rectangle2D.Double(GConst.FACT_X, GConst.FACT_Y, GConst.FACT_D,
                GConst.FACT_D), (byte) 0);
    entities.add(theFactory);
    renderable.add(theFactory.shape());
    theTurret =
        new GunTurret(new double[] {GConst.TRT_X, GConst.TRT_Y}, 0.0,
            new double[] {0, 0}, 0.0, new double[] {0, 0}, "Rectangle",
            new Rectangle2D.Double(GConst.TRT_X, GConst.TRT_Y, GConst.TRT_W,
                GConst.TRT_H), (byte) 0);
    entities.add(theTurret);
    renderable.add(theTurret.shape());
    theSphere =
        new GoalSphere(new double[] {GConst.SPH_X, GConst.SPH_Y}, 0.0,
            new double[] {0, 0}, GConst.SPH_MASS, new double[] {0, 0},
            "Ellipse", new Ellipse2D.Double(GConst.SPH_X, GConst.SPH_Y,
                GConst.SPHERE_D, GConst.SPHERE_D), (byte) 1);
    entities.add(theSphere);
    renderable.add(theSphere.shape());
    theFuelPod =
        new FuelPod(new double[] {GConst.POD_X, GConst.POD_Y}, 0.0,
            new double[] {0, 0}, 0.0, new double[] {0, 0}, "Ellipse",
            new Ellipse2D.Double(GConst.POD_X, GConst.POD_Y, GConst.POD_D,
                GConst.POD_D), (byte) 0);
    entities.add(theFuelPod);
    renderable.add(theFuelPod.shape());
  }

  private static void updateShape(final DynamicEntity the_entity) {
    final RectangularShape shape = (RectangularShape) the_entity.shape();
    shape.setFrame(the_entity.position()[0], the_entity.position()[1],
          shape.getWidth(), shape.getHeight());
  }

  public static void thrust() {
    playerShip.acceleration(new double[] {
      playerShip.acceleration()[0] + GConst.ACC_GAIN *
          Math.sin(Math.toRadians(playerShip.orientation())),
      playerShip.acceleration()[1] + GConst.ACC_GAIN *
          Math.cos(Math.toRadians(playerShip.orientation()))});
    playerShip.set_fuel_content(playerShip.fuel() - 1);
    if (playerShip.towed()) {
      theSphere.acceleration(playerShip.acceleration());
      theSphere.velocity(playerShip.velocity());
      theSphere.orientation(playerShip.orientation());
    }
  }

  public static void quit() {
    mainFrame.dispose();
    System.exit(1);
  }

  public static void turnRight() {
    final int my_turnamount = 10;
    final int my_fullcircle = 360;
    playerShip.orientation(playerShip.orientation() - my_turnamount);
    if (playerShip.orientation() < 0) {
      playerShip.orientation(my_fullcircle + playerShip.orientation());
    }
  }

  public static void turnLeft() {
    final int my_turnamount = 10;
    final int my_fullcircle = 360;
    playerShip.orientation(playerShip.orientation() + my_turnamount);
    if (playerShip.orientation() > my_fullcircle) {
      playerShip.orientation(my_fullcircle - playerShip.orientation());
    }
  }

  public static void fire() {
    if (bulletCount < NUM_BULLETS) {
      final Bullet bull =
          new Bullet(playerShip.position(), playerShip.orientation(),
              new double[] {0, 0}, 0.0, new double[] {
                GConst.BUL_VEL *
                    Math.sin(Math.toRadians(playerShip.orientation())),
                GConst.BUL_VEL *
                    Math.cos(Math.toRadians(playerShip.orientation()))},
              "Rectangle", new Rectangle2D.Double(playerShip.position()[0],
                  playerShip.position()[1], 2, 2), (byte) 0);
      playerBullets.add(bull);
      bulletCount++;
    }
  }

  public static void activateShield() {
    shieldOn = true;
  }

  private static void sleep() {
    final int my_sleeptime = 30;
    try {
      Thread.sleep(my_sleeptime);
    } catch (InterruptedException e) {
      e.printStackTrace(System.err);
    }
  }

  public static byte state() {
    return my_state;
  }

  /**
   * The graphics component of the game.
   * Responsible for rendering all the shapes of the entities.
   */
  private static class GameDraw extends JComponent {
    /**
     * Standard serial version UID.
     */
    private static final long serialVersionUID = 1L;
    /**
     * The shapes that the component is to render.
     */
    private transient List my_shapes;

    public GameDraw(final List the_list) {
      super();
      my_shapes = the_list;
    }

    protected void paintComponent(final Graphics the_graphics) {
      final Graphics2D graph2 = (Graphics2D) the_graphics;
      graph2.setColor(Color.BLACK);
      graph2.draw((Shape)my_shapes.get(0));
      graph2.fill((Shape) my_shapes.get(0));
      graph2.setColor(Color.GREEN);
      final int size = my_shapes.size();
      for (int i = 1; i < size; ++i) {
        graph2.draw((Shape) my_shapes.get(i));
        graph2.fill((Shape) my_shapes.get(i));
      }
    }

    public void updateShapes(final List the_array) {
      my_shapes = the_array;
    }
  }

  /**
   * The key listener.
   */
  private static class MainKeys implements KeyListener {
  /**
   * The last key pressed.
   */
    private transient int my_key;

    public MainKeys() {
      my_key = 0;
    }

    public void keyPressed(final KeyEvent the_key) {
      my_key = the_key.getKeyCode();
    }

    public void keyReleased(final KeyEvent the_key) {
      my_key = -1;
    }

    public void keyTyped(final KeyEvent the_key) {

    }

    public int lastKeyPressed() {
      return my_key;
    }
  }
}
