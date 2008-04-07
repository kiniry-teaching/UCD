
package thrust.audio;

import  sun.audio.*;    //import the sun.audio package
import  java.io.*;


/**
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music {
  //@ public model boolean is_playing;

  FileInputStream myMusicFile = new FileInputStream();
  AudioStream mySong = new AudioStream(myMusicFile);
  /**
   * 
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {
    assert false; //@ assert false;
    return false;
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    
    AudioPlayer.player.start(mySong); 
    
    assert false; //@ assert false;
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
   
    AudioPlayer.player.stop(mySong);
    assert false; //@ assert false;
  }
}
