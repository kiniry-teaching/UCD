/*
 * A re-implementation of the classic C=64 game 'Thrust'. @author "Joe Kiniry
 * (kiniry@acm.org)" @module "COMP 20050, COMP 30050" @creation_date "March
 * 2007" @last_updated_date "April 2008" @keywords "C=64", "Thrust", "game"
 */

package thrust;

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

import javax.swing.JComponent;
import javax.swing.JFrame;
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
import thrust.input.InputHandler;

/**
 * Simulating all of the entities in the game to realize the game.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public final class Main {

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
    started = false;
    createWelcomeScreen();
    displayHighScores();
    initializeEntities();
    while (true) {
      input.process((char) inputListener.lastKeyPressed());
      if (started) {
        cycleEntities();
        drawComponent.updateShapes(renderable);
      }
      mainFrame.update(mainFrame.getGraphics());
      sleep();
    }
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
    final int my_height = 600;
    final int my_width = 800;
    started = false;
    if (mainFrame != null) {
      mainFrame.dispose();
    }
    mainFrame = new JFrame("Thrust");
    mainFrame.setSize(my_width, my_height);
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
    game = new GameState();
    input = new InputHandler();
  }

  private static void cycleEntities() {
    final int my_dirlen = 25;
    final double my_simulatetime = 0.1;
    renderable = new ArrayList();
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
    for (int i = 0; i < entities.size(); ++i) {
      if (!(entities.get(i) instanceof StaticEntity)) {
        ((DynamicEntity) entities.get(i)).simulate(my_simulatetime);
        updateShape((DynamicEntity) entities.get(i));
      }
      renderable.add(((Entity) entities.get(i)).shape());
      if (entities.get(i) instanceof Bullet) {
        final Bullet bull = (Bullet) entities.get(i);
        if (!mapBounds.contains(bull.position()[0], bull
            .position()[1])) {
          entities.remove(i);
          bulletCount--;
        }
      }
    }
  }

  public static void createGameScreen() {
    final int my_width = 800;
    final int my_height = 600;
    started = true;
    if (mainFrame != null) {
      mainFrame.dispose();
    }
    mapBounds = new Rectangle2D.Double(0, 0, my_width, my_height);
    drawComponent = new GameDraw(renderable);
    bulletCount = 0;
    mainFrame = new JFrame("Thrust");
    mainFrame.setVisible(true);
    mainFrame.setSize(my_width, my_height);
    mainFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    mainFrame.add(drawComponent);
    mainFrame.update(mainFrame.getGraphics());
    mainFrame.addKeyListener(inputListener);
  }

  private static void initializeEntities() {
    renderable = new ArrayList();
    entities = new ArrayList();
    renderable.add(mapBounds);
    playerShip =
        new Spaceship(new double[] {450, 500}, 0, new double[] {0, 0},
            Spaceship.EMPTY_MASS + Spaceship.INITIAL_FUEL, new double[] {0, 0},
            "Triangle", new Ellipse2D.Double(450, 500, 20, 20), (byte) 0);
    entities.add(playerShip);
    renderable.add(playerShip.shape());
    theFactory =
        new Factory(new double[] {450, 60}, 0.0, new double[] {0, 0}, 0.0,
            new double[] {0, 0}, "Rectangle", new Rectangle2D.Double(450, 60,
                60, 60), (byte) 0);
    entities.add(theFactory);
    renderable.add(theFactory.shape());
    theTurret =
        new GunTurret(new double[] {280, 20}, 0.0, new double[] {0, 0}, 0.0,
            new double[] {0, 0}, "Rectangle", new Rectangle2D.Double(280, 20,
                60, 20), (byte) 0);
    entities.add(theTurret);
    renderable.add(theTurret.shape());
    theSphere =
        new GoalSphere(new double[] {400, 40}, 0.0, new double[] {0, 0},
            10000.0, new double[] {0, 0}, "Ellipse", new Ellipse2D.Double(400,
                40, 20, 20), (byte) 0);
    entities.add(theSphere);
    renderable.add(theSphere.shape());
    theFuelPod =
        new FuelPod(new double[] {720, 20}, 0.0, new double[] {0, 0}, 0.0,
            new double[] {0, 0}, "Ellipse", new Ellipse2D.Double(720, 20, 20,
                20), (byte) 0);
    entities.add(theFuelPod);
    renderable.add(theFuelPod.shape());
  }

  private static void updateShape(final DynamicEntity the_entity) {
    final RectangularShape shape = (RectangularShape) the_entity.shape();
    shape
        .setFrame(the_entity.position()[0], the_entity.position()[1],
          shape.getWidth(), shape.getHeight());
  }

  public static void thrust() {
    playerShip.acceleration(new double[] {
      playerShip.acceleration()[0] + 1 *
          Math.sin(Math.toRadians(playerShip.orientation())),
      playerShip.acceleration()[1] + 1 *
          Math.cos(Math.toRadians(playerShip.orientation()))});
  }

  public static void quit() {
    mainFrame.dispose();
    System.exit(1);
  }

  public static void turnLeft() {
    final int my_turnamount = 25;
    final int my_fullcircle = 360;
    playerShip.orientation(playerShip.orientation() - my_turnamount);
    if (playerShip.orientation() < 0) {
      playerShip.orientation(my_fullcircle + playerShip.orientation());
    }
  }

  public static void turnRight() {
    final int my_turnamount = 25;
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
                50 * Math.sin(Math.toRadians(playerShip.orientation())),
                50 * Math.cos(Math.toRadians(playerShip.orientation()))},
              "Rectangle", new Rectangle2D.Double(playerShip.position()[0],
                  playerShip.position()[1], 2, 2), (byte) 0);
      entities.add(bull);
      bulletCount++;
    }
  }

  private static void sleep() {
    final int my_sleeptime = 30;
    try {
      Thread.sleep(my_sleeptime);
    } catch (InterruptedException e) {
      e.printStackTrace(System.err);
    }
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
      final int size = my_shapes.size();
      for (int i = 0; i < size; ++i) {
        graph2.draw((Shape) my_shapes.get(i));
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

    }

    public void keyTyped(final KeyEvent the_key) {

    }

    public int lastKeyPressed() {
      final int temp = my_key;
      my_key = -1;
      return temp;
    }
  }
}
