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
import java.awt.Color;

import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

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
 * 
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public final class Main {
  /**
   * This class cannot be constructed.
   */
  private Main() {
    assert false; // @ assert false;
  }

  /**
   * The main screen frame.
   */
  private static JFrame mainFrame;
  private static JTextArea console;
  private static JScrollPane scroll;
  private static MainKeys inputListener;
  private static GameState game;
  private static InputHandler input;
  private static Rectangle2D.Double mapBounds;
  private static Spaceship playerShip;
  private static Factory theFactory;
  private static GunTurret theTurret;
  private static GoalSphere theSphere;
  private static FuelPod theFuelPod;
  private static gameDraw dr;
  private static JFrame newFr;
  private static Bullet[] bullets;
  private static final int NUM_BULLETS = 4;
  //private static Shape[] renderable;
  private static boolean started;
  
  /**
   * Run the game.
   * 
   * @param the_args
   *          The command-line arguments are ignored.
   */
  public static void main(final String[] the_args) {
    // display the title screen
    started = false;
    mainFrame = new JFrame("Thrust");
    mainFrame.setSize(500, 500);
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
    // play title music
    // Music music = new Music();
    game = new GameState();
    // music.make(new File("media/music.mp3"));
    // music.start();
    // wait for keyboard input
    // repeat the following until the player asks to quit
    for (int i = 0; i < game.high_scores().length; ++i) {
      console.setText(" " + game.high_score(i).score() + "\n"
                      + console.getText());
      for (int j = 0; j < game.high_score(i).initials().length; ++j) {
        console.setText(game.high_score(i).initials()[j] + console.getText());
      }
    }
    while(!started) {
      sleep(100);
    }
    init();
    // show the high score display
    while (true) {
      input.process((char) inputListener.lastKeyPressed());
      playerShip.simulate(0.1);
      final Ellipse2D.Double plShape = (Ellipse2D.Double)playerShip.shape();
      plShape.setFrame(playerShip.position()[0], playerShip.position()[1], plShape.width, plShape.height);
      for(int i = 0; i < NUM_BULLETS; ++i) {
        if(bullets[i] != null) {
           bullets[i].simulate(0.1);
           final Rectangle2D.Double bulletShape = (Rectangle2D.Double)bullets[i].shape();
           bulletShape.setRect(bullets[i].position()[0], bullets[i].position()[1], bulletShape.width, bulletShape.height);
           bullets[i].shape(bulletShape);
           if(!mapBounds.contains((Rectangle2D.Double)bullets[i].shape())) {
             bullets[i] = null;
           }
        }
      }
      final Line2D.Double orientLine = new Line2D.Double(new Point2D.Double(plShape.getCenterX(), plShape.getCenterY()), 
                                                   new Point2D.Double((plShape.getCenterX() + 25 * Math.sin(Math.toRadians(playerShip.orientation()))), 
                                                                      (plShape.getCenterY() + 25 * Math.cos(Math.toRadians(playerShip.orientation())))));
      
      dr.updateShapes(new Shape[] {mapBounds, plShape, theFactory.shape(),
                 theTurret.shape(), theSphere.shape(), theFuelPod.shape(), orientLine}, bullets);
      //console.setText("a: ["+playerShip.acceleration()[0] +", "+ playerShip.acceleration()[1]+"] v: ["+playerShip.velocity()[0] +", "+ playerShip.velocity()[1]+"]\n"+ console.getText());
      
      if(!mapBounds.contains(new Point2D.Double(plShape.getCenterX(), plShape.getCenterY()))) {
        console.setText("outtabounds");
        newFr.dispose();
      }
      newFr.update(newFr.getGraphics());
      mainFrame.update(mainFrame.getGraphics());
      sleep(30);
      // wait for input to start the game
      // repeat the following until the player is out of lives or asks to quit:
      // record the current time T
      // perform a step in the simulation
      // render all entities
      // process the next keyboard input
      // record the current time T'
      // wait for (1/30th of a second - (T-T'))
      // remove the game interface
      // if the player has a new high score
      // ask them to input their initials
      // save the new high score
    }
  }

  private static void init() {
    mapBounds = new Rectangle2D.Double(0, 0, 800, 600);
    playerShip = new Spaceship(new double[] { 450, 500 }, 0, new double[] { 0,0 },
                               Spaceship.EMPTY_MASS + Spaceship.INITIAL_FUEL,
                               new double[] { 0, 0 }, "Triangle",
                               new Ellipse2D.Double(450, 500, 20, 20),
                               (byte) 0);
    theFactory = new Factory(new double[] {450, 60}, 0.0,
                 new double[] {0, 0}, 0.0,
                 new double[] {0, 0}, "Rectangle",
                 new Rectangle2D.Double(450, 60, 60, 60), (byte) 0);
    theTurret = new GunTurret(new double[] {280, 20}, 0.0,
                 new double[] {0, 0}, 0.0,
                 new double[] {0, 0}, "Rectangle",
                 new Rectangle2D.Double(280, 20, 60, 20), (byte) 0);
    theSphere = new GoalSphere(new double[] {400, 40}, 0.0,
                 new double[] {0, 0}, 10000.0,
                 new double[] {0, 0}, "Ellipse",
                 new Ellipse2D.Double(400, 40, 20, 20), (byte) 0);
    theFuelPod = new FuelPod(new double[] {720, 20}, 0.0,
                 new double[] {0, 0}, 0.0,
                 new double[] {0, 0}, "Ellipse",
                 new Ellipse2D.Double(720, 20, 20, 20), (byte) 0);
    dr = new gameDraw(new Shape[] {playerShip.shape(), theFactory.shape(),
                 theTurret.shape(), theSphere.shape(), theFuelPod.shape(), mapBounds});
    bullets = new Bullet[NUM_BULLETS];
    newFr = new JFrame();
    newFr.setVisible(true);
    newFr.setSize(800, 600);
    newFr.add(dr);
    newFr.update(newFr.getGraphics());
    newFr.addKeyListener(inputListener);
  }
  
  public static void thrust() {
    playerShip.acceleration(new double[] {playerShip.acceleration()[0] + 1 * Math.sin(Math.toRadians(playerShip.orientation())), playerShip.acceleration()[1] + 1 * Math.cos(Math.toRadians(playerShip.orientation()))});
  }

  public static void quit() {
    mainFrame.dispose();
    System.exit(1);
  }

  public static void turnLeft() {
    playerShip.orientation(playerShip.orientation() - 25);
    if(playerShip.orientation() < 0) {
      playerShip.orientation(360 + playerShip.orientation());
    }
  }
  
  public static void turnRight() {
    playerShip.orientation(playerShip.orientation() + 25);
    if(playerShip.orientation() > 360) {
      playerShip.orientation(360 - playerShip.orientation());
    }
  }
  
  public static void fire() {
    int i;
    for(i = 0; i < NUM_BULLETS; ++i) {
      if (bullets[i] == null) {
        break;
      }
    }
    if(i < NUM_BULLETS) {
      bullets[i] = new Bullet(playerShip.position(), playerShip.orientation(), new double[] {0, 0},
                              0.0, new double[] {50 * Math.sin(Math.toRadians(playerShip.orientation())),
                                                 50 * Math.cos(Math.toRadians(playerShip.orientation()))},
                                                 "Rectangle", new Rectangle2D.Double(playerShip.position()[0], playerShip.position()[1], 2, 2), (byte)0);
    }
  }
  
  public static void start() {
    started = true;
  }
  
  private static void sleep(final int amnt) {
    try{
      Thread.sleep(amnt);
    } catch (InterruptedException e) {
      e.printStackTrace(System.err);
    }
  }
  
  private static class gameDraw extends JComponent {
    private static final long serialVersionUID = 1L;
    private transient Shape[] shapes;
    private transient Bullet[] bull;
    public gameDraw(final Shape[] arr) {
      super();
      shapes = new Shape[arr.length];
      System.arraycopy(arr, 0, shapes, 0, arr.length);
      bull = new Bullet[0];
    }
    
    protected void paintComponent(final Graphics g) {
      final Graphics2D graph2 = (Graphics2D) g;
      graph2.setColor(Color.BLACK);
      graph2.draw(shapes[0]);
      graph2.fill(shapes[0]);
      graph2.setColor(Color.GREEN);
      for(int i = 1; i < shapes.length; ++i) {
        graph2.draw(shapes[i]);
        graph2.fill(shapes[i]);
      }
      graph2.setColor(Color.RED);
      for(int i = 0; i < bull.length; ++i) {
        if(bull[i] != null) {
          graph2.draw(bull[i].shape());
          graph2.fill(bull[i].shape());
        }
      }
    }
    
    public void updateShapes(final Shape[] arr, final Bullet[] bul) {
      shapes = new Shape[arr.length];
      System.arraycopy(arr, 0, shapes, 0, arr.length);
      bull = new Bullet[bul.length];
      System.arraycopy(bul, 0, bull, 0, bul.length);
    }
  }
  
  private static class MainKeys implements KeyListener {

    private transient int myKey;

    public void keyPressed(final KeyEvent key) {
      myKey = key.getKeyCode();
    }

    public void keyReleased(final KeyEvent arg0) {
      
    }

    public void keyTyped(final KeyEvent arg0) {
      
    }

    public int lastKeyPressed() {
      final int temp = myKey;
      myKey = -1;
      return temp;
    }

    public MainKeys() {
      myKey = 0;
    }
  }
}
