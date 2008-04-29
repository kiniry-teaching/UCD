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
import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
import java.io.IOException;
import javax.sound.sampled.UnsupportedAudioFileException;
import javax.sound.sampled.LineUnavailableException;
/**
 * In-game music.
 * @author Nicholas McCarthy (nicholas.mccarthy@gmail.com)
 * @author Stephen Murphy (Stephen.Murphy.1@ucdconnect.ie)
 * @version 25 April 2008 */

public class Music {

  /** Location of .wav file. */
  private static final String MUSIC_LOCATION =
    "../../../media/Thrust_music.wav";
/** Boolean for checking if music is playing. */
  private transient boolean my_music_boolean = true;
/** Creates music_file File. */
  private transient File my_music_file;
  /** AudioInputStream to take my_music_file. */
  private transient AudioInputStream my_music_stream;
  /** Takes the audio format of the AudioInputStream. */
  private transient AudioFormat my_music_format;
  /** The clip that gets played. */
  private transient Clip my_music_clip;

  public Music() { // Fixed try indentation but now method is >15 lines..
    my_music_file = new File(MUSIC_LOCATION);
    try {
      my_music_stream = AudioSystem.getAudioInputStream (my_music_file);
    } catch (UnsupportedAudioFileException e) {
      return;
    } catch (IOException e)  {
      return;
    }
    my_music_format = my_music_stream.getFormat();
    final DataLine.Info info = new DataLine.Info(Clip.class, my_music_format);
    try {
      my_music_clip = (Clip)AudioSystem.getLine(info);
    } catch (LineUnavailableException e) {
      return;
    }
  }

  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public boolean playing() {

    return my_music_boolean;

  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    // replaced my_music.start(); with .loop.
    // Clip.LOOP_CONTINUOUSLY defined in Clip class.
    my_music_clip.loop(Clip.LOOP_CONTINUOUSLY);
    my_music_boolean = true;

  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {

    my_music_clip.stop();
    my_music_clip.flush();
    my_music_boolean = false;

  }
}
