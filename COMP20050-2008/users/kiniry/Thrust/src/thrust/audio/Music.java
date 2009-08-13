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
import javax.sound.sampled.*;

/**
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music {
  //@ public model boolean is_playing;
  /** A state flag tracking whether music is playing. */
  private transient /*@ spec_public @*/ boolean my_music_is_playing = true;
  //@ represents is_playing <- my_music_is_playing;

  private final /*@ non_null @*/ AudioFileFormat my_audio_file_format;
  private final /*@ non_null @*/ AudioFormat my_audio_format;
  private final /*@ non_null @*/ DataLine.Info my_data_line_info;
  private final /*@ non_null @*/ Port my_port;
  private final /*@ non_null @*/ SourceDataLine my_source_data_line;
  private final /*@ non_null @*/ Clip my_clip;

  /**
   * @param the_mp3_file Create a new music object that controls
   * playing of this game music.
   */
  public Music(final /*@ non_null @*/ String the_mp3_file)
    throws FileNotFoundException {
    final File the_music_file = new File(the_mp3_file);
    if (the_music_file.exists() & the_music_file.canRead()) {
      // create an audio clip from this file
      if (!AudioSystem.isLineSupported(info)) {
        // Handle the error.
        }
        // Obtain and open the line.
    try {
      my_audiofileformat = AudioFileFormat.getAudioFileFormat(the_music_file);
      my_audioformat = new AudioFormat();
      my_dataline_info = new DataLine.Info(Clip.class, my_audioformat)
        line = (TargetDataLine) AudioSystem.getLine(info);
        line.open(format);
    } catch (LineUnavailableException ex) {
        // Handle the error.
        //... 
    }
      assert false;
    } else {
      throw new FileNotFoundException();
    }
  }

  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {
    return my_music_is_playing;
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    my_music_is_playing = true;
    if (my_music != null) {
      my_music.play();
    }
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    my_music_is_playing = false;
    if (my_music != null) {
      my_music.stop();
    }
  }
}
