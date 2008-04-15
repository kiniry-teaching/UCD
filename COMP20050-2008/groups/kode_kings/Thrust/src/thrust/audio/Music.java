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
 * @author JCiaran Hale (Ciaran.hale@ucdconnect.ie)
 * @version 15 April 2008
 */
public class Music {
  //@ public model boolean is_playing;
  /**
   *indicates the music file to load.
   */
  private final transient File my_clipFile = new File("");
  /**
   * the name of our new file.
   */
  private transient Clip my_clip;

  public Music() throws Exception {
    AudioInputStream my_audio_input_stream = null;

    final DataLine.Info info =
      new DataLine.Info(SourceDataLine.class,
        my_audio_input_stream.getFormat());



    my_audio_input_stream = AudioSystem.getAudioInputStream(my_clipFile);

    my_clip = (Clip) AudioSystem.getLine(info);

    my_clip.open(my_audio_input_stream);
  }
    /**
     * @return Is music playing?
    */
    //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {

    return false;
  }
  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    my_clip.loop(Clip.LOOP_CONTINUOUSLY);

  }

 /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    my_clip.stop();

  }
}
