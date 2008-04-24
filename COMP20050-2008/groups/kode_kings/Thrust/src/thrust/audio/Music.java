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

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.SourceDataLine;
import javax.sound.sampled.UnsupportedAudioFileException;


/**
 * In-game music.
 * @author Ciaran Hale (Ciaran.hale@ucdconnect.ie)
 * @version 24 April 2008
 */
public class Music {
  //@ public model boolean is_playing;
  /**
   *indicates the music file to load.
   */
  private final transient File my_thrust_music =
    new File("/Thrust/Thrust/media/music.mp3");
  /**
   * the name of our new file.
   */
  private transient Clip my_song;

  public Music() throws Exception {
    final AudioInputStream my_audio_song =
      AudioSystem.getAudioInputStream(my_thrust_music);


    my_song.open(my_audio_song);
  }
    /**
     * @return Is music playing?
    */
    //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {

    return my_song.isRunning();
  }
  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    my_song.loop(Clip.LOOP_CONTINUOUSLY);

  }

 /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    my_song.stop();

  }
}


