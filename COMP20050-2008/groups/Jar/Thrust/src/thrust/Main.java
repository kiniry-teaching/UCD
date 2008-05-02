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
import thrust.input.KeyBoardInput;

/**
 * Simulating all of the entities in the game to realize the game.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public final class Main {
  /** Game state. */
  public static final thrust.entities.about.GameState GAMESTATE =
    new thrust.entities.about.GameState();
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
    //   repeat the following until the player is out of lives or asks to quit:
    do {
      if (GAMESTATE.get_state() == GameState.PLAY) {
        while (GAMESTATE.lives() > 0 &&
            GAMESTATE.get_state() == GameState.PLAY) {
          //      record the current time T
          time = System.currentTimeMillis();
          //      perform a step in the simulation
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
          INPUT.INPUT.check(true);
        }
      }
    } while(GAMESTATE.get_state() != GameState.PLAY);
    //   remove the game interface
    //   if the player has a new high score
    //     ask them to input their initials
    //     save the new high score
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
          if (!area.isEmpty()) {
            final Explosion explose = new Explosion();
            explose.set_static_state(the_enemy.position(),
                                     the_enemy.orientation(),
                                     "Explosion",
                                     the_enemy.shape().getBounds2D(),
                                     (byte)0);
            my_entities.add(explose);
            my_entities.remove(the_enemy);
          }
        }
      }
      if (the_entity instanceof DynamicEntity) {
        ((DynamicEntity) the_entity).simulate(1);
      }
    }
  }

  private static void render() {
    my_iterator = my_entities.iterator();
    while (my_iterator.hasNext()) {
      ((Entity) my_iterator.next()).render();
    }
  }
}
