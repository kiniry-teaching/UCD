/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust;

import java.awt.geom.Area;
import java.awt.geom.Rectangle2D;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.logging.Logger;
import thrust.audio.Music;
import thrust.entities.DynamicEntity;
import thrust.entities.Entity;
import thrust.entities.about.GameState;
import thrust.entities.in_game.Bullet;
import thrust.entities.in_game.Explosion;
import thrust.entities.in_game.Spaceship;
import thrust.input.KeyBoardInput;

/**
 * Simulating all of the entities in the game to realize the game.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public final class Main {
  /** The spaceship entity. */
  public static final Spaceship SPACESHIP = new Spaceship();
  /** Game state. */
  public static final GameState GAMESTATE =
    new GameState();
  /** The music player. */
  public static final Music MUSIC = new Music();
  /** The input handler. */
  public static final KeyBoardInput INPUT = new KeyBoardInput();
  /** */
  private static Collection my_entities = new LinkedList();
  /** Logger. */
  private static final Logger LOG = Logger.getLogger("Main");
  /** 1/30th of a second. */
  private static final long TICK = 33;
  /** Iterator for rendering etc. */
  private static transient Iterator my_iterator;
  /** */
  private static long time;

  /** This class cannot be constructed. */
  private Main() {
    //@ assert true;
  }
  /**
   * Run the game.
   * @param the_args The command-line arguments are ignored.
   */
  public static void main(final String[] the_args) {
    LOG.info("Title Screen");
    // display the title screen
    MUSIC.start();
    // wait for keyboard input
    // repeat the following until the player asks to quit
    //   show the high score display
    //   wait for input to start the game
    //   create game map and initialize location of all entities
    SPACESHIP.set_dynamic_state(new double[]{0, 0} , 0,
                                new double[]{0, 0}, 0, 0, new double[]{0, 0});
    SPACESHIP.set_state("Triangle?",
                        new Rectangle2D.Double(0, 1, 2, 3), (byte)0);
    my_entities.add(SPACESHIP);
    //   repeat the following until the player is out of lives or asks to quit:
    do {
      if (GAMESTATE.get_state() == GameState.PLAY) {
        while (GAMESTATE.lives() > 0 &&
            GAMESTATE.get_state() == GameState.PLAY) {
          //      record the current time T
          time = System.currentTimeMillis();
          //      perform a step in the simulation
          simulateShip();
          simulate();
          //      render all entities
          render();
          //      process the next keyboard input
          //      record the current time T'
          try {
            Thread.sleep(TICK - (System.currentTimeMillis() - time));
          } catch (InterruptedException e) {
            LOG.severe(e.getMessage());
          }
          //      wait for (1/30th of a second - (T-T'))
        }
      }
    } while(GAMESTATE.get_state() != GameState.QUIT);
    //   remove the game interface
    //   if the player has a new high score
    //     ask them to input their initials
    //     save the new high score
    System.exit(0);
  }

  private static void simulate() {
    my_iterator = my_entities.iterator();
    final Iterator enemy = my_entities.iterator();
    Entity the_entity;
    while (my_iterator.hasNext()) {
      the_entity = (Entity)my_iterator.next();
      if (the_entity instanceof Bullet) {
        while (enemy.hasNext()) {
          final DynamicEntity the_enemy = ((DynamicEntity)enemy.next());
          final Area area = new Area(the_entity.shape());
          area.intersect(new Area(the_enemy.shape()));
          if (!area.isEmpty() && !the_enemy.equals(the_entity)) {
            final Explosion explose = new Explosion();
            explose.set_static_state(the_enemy.position(),
                                     the_enemy.orientation(),
                                     "Explosion",
                                     the_enemy.shape().getBounds2D(),
                                     (byte)0);
            my_entities.add(explose);
            my_entities.remove(the_enemy);
            my_entities.remove(enemy);
            break;
          }
        }
      }
      if (the_entity instanceof DynamicEntity) {
        ((DynamicEntity) the_entity).simulate(1);
      }
    }
  }

  private static void simulateShip() {
    my_iterator = my_entities.iterator();
    while (my_iterator.hasNext()) {
      final Entity the_entity = ((Entity)my_iterator.next());
      final Area area = new Area(SPACESHIP.shape());
      area.intersect(new Area(the_entity.shape()));
      if (!area.isEmpty() && !SPACESHIP.equals(the_entity)) {
        final Explosion explose = new Explosion();
        explose.set_static_state(SPACESHIP.position(),
                                 SPACESHIP.orientation(),
                                 "Explosion",
                                 SPACESHIP.shape().getBounds2D(),
                                 (byte)0);
        my_entities.add(explose);
        my_entities.remove(SPACESHIP);
        GAMESTATE.change_lives((byte)-1);
        if (the_entity instanceof Bullet) {
          my_entities.remove(the_entity);
        }
        break;
      }
    }
  }

  private static void render() {
    my_iterator = my_entities.iterator();
    while (my_iterator.hasNext()) {
      ((Entity)my_iterator.next()).render();
    }
  }

  private static void fire() {
    final Bullet bull = new Bullet();
    bull.set_dynamic_state(new double[]{0, 0} , 0,
                                new double[]{0, 0}, 0, 0, new double[]{0, 0});
    bull.set_state("Bullet",
                        new Rectangle2D.Double(1, 1, 1, 1), (byte)0);
    my_entities.add(bull);
  }
}
