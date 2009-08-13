/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.audio;

import java.applet.Applet;
import java.io.File;
import java.util.logging.ConsoleHandler;
import java.util.logging.Logger;
import java.net.URL;
import java.net.MalformedURLException;

/**
 * An applet used to test classes in the thrust.audio package.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 24 April 2008
 */
public class AudioTestApplet extends Applet {
  /** One second is 1000 miliseconds. */
  private static final long ONE_SECOND = 1000;

  /** The default serialVersionUID. */
  private static final long serialVersionUID = 1L;

  /** The game music under test. */
  private transient /*@ non_null @*/ Music my_game_music;

  /* The game sound effects. */
  /** The engine sound effect. */
  private transient /*@ non_null @*/ SoundEffect my_engine_sound_effect;
  /** The shield sound effect. */
  private transient /*@ non_null @*/ SoundEffect my_shield_sound_effect;
  /** The fire gun sound effect. */
  private transient /*@ non_null @*/ SoundEffect my_fire_gun_sound_effect;

  /** {@inheritDoc} */
  public void init() {
    Logger.global.addHandler(new ConsoleHandler());
    Logger.global.info("AudioTestApplet started.");
    try {
      my_game_music =
        new Music(getAudioClip(new URL("file:media/music.mp3")));
      my_engine_sound_effect = new SoundEffect(new File("media/engine.mp3"));
      my_shield_sound_effect = new SoundEffect(new File("media/shield.mp3"));
      my_fire_gun_sound_effect =
        new SoundEffect(new File("media/fire_gun.mp3"));
    } catch (MalformedURLException mue) {
      assert false; //@ assert false;
    }
  }

  /** {@inheritDoc} */
  public void start() {
    test_music();
    test_effects();
  }

  /** Test playing all sound effects, both in sequence and in parallel. */
  private void test_effects() {
    my_engine_sound_effect.start();
    my_shield_sound_effect.start();
    my_fire_gun_sound_effect.start();
  }

  /** Test playing and stopping game music. */
  private void test_music() {
    try {
      my_game_music.start();
      Thread.sleep(ONE_SECOND);
      my_game_music.stop();
      Thread.sleep(ONE_SECOND);
    } catch (InterruptedException io) {
      assert false; //@ assert false;
    }
  }
}
