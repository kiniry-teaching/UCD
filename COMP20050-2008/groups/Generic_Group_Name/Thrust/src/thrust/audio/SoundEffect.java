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
import sun.audio.*;    //import the sun.audio package
import java.io.*;

import java.io.File;

public class SoundEffect {

  InputStream in1 = new FileInputStream('colt45.mp3');
  AudioStream as1 = new AudioStream(in1); 

  InputStream in2 = new FileInputStream('explosion.mp3');
  AudioStream as2 = new AudioStream(in2); 

  InputStream in3 = new FileInputStream('fuse.wav');
  AudioStream as3 = new AudioStream(in3); 

  InputStream in4 = new FileInputStream('chain.mp3');
  AudioStream as4 = new AudioStream(in4); 

  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in the provided file.
   */
  public /*@ pure @*/ SoundEffect(File the_sound_effect_file) {
    assert false; //@ assert false;
  }

  /**
   * Start playing your effect.
   */
  public void start(AudioStream as) {
    AudioPlayer.player.start(as);
  }

  public void fire() {
    start(as1);
  }

  public void explode() {
    start(as2);
  }

  public void thrust() {
    start(as3);
  }

  public void chain() {
    start(as4);
  }

}
