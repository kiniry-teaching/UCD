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
  /**
   * @author David McGinn
   * @author Cillian O'Neill
   * @author Michael Fahey
   * @version 2 May 2008
   */

  try {
  
  public InputStream in1 = new FileInputStream("colt45.mp3");
  public AudioStream as1 = new AudioStream(in1); 

  public InputStream in2 = new FileInputStream("explosion.mp3");
  public AudioStream as2 = new AudioStream(in2); 

  public InputStream in3 = new FileInputStream("fuse.wav");
  public AudioStream as3 = new AudioStream(in3); 

  public InputStream in4 = new FileInputStream("chain.mp3");
  public AudioStream as4 = new AudioStream(in4); 
  
  } catch (Exception e){}

  
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in the provided file.
   */
//  public SoundEffect(File the_sound_effect_file) {
//    assert false; //@ assert false;
//  }
  
    public SoundEffect() {
      
    }

  /**
   * Start playing your effect.
   */
  public void start(AudioStream as) {
    AudioPlayer.player.start(as);
  }

  public void fire() {
    start(as1);
    System.out.println("FIRING");
  }

  public void explode() {
    start(as2);
    System.out.println("EXPLODING");
  }

  public void thrust() {
    start(as3);
    System.out.println("THRUSTING");
  }

  public void chain() {
    start(as4);
    System.out.println("CHAIN EXTENDING");
  }
  
}
