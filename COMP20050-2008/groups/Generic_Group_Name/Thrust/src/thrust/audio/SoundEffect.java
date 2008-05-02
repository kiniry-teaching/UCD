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
   * Your sound effect is 's'.
   * @param s the sound effect to make.
   */
  public /*@ pure @*/ SoundEffect make(File s) {
 //   assert false; //@ assert false;
    return null;
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
