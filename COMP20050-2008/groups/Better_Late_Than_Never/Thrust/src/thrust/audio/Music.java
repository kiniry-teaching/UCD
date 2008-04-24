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

/**
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */

import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.UnsupportedAudioFileException;


import java.io.File;
import java.io.IOException;



public class Music {
  //@ public model boolean is_playing;

  private transient Clip our_clip;
  
  /**
   * Indication as to whether or not the music is playing
   */
  
  private transient Clip our_clip;
  //@ ensures \result == is_playing;
  
    /**
     * The In-Game music. @ i.e the sound file java.io input provided @
     */

  private final transient File our_soundFile = new File("Thrust_music.wav");
  
  
  
  
  
  
  
  public /*@ pure @*/ boolean playing() {
    assert false; //@ assert false;
    return false;
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    assert false; //@ assert false;
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    assert false; //@ assert false;
  }
}
