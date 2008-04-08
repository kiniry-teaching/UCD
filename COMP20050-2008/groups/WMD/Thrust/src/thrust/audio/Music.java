package thrust.audio;

import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.UnsupportedAudioFileException;

import java.io.File;
import java.io.IOException;

/** File for music.
 * @author Stephen Walker (stephen.walker@ucdconnect.ie).
 * @version 8 April 2008
 *  */
public class Music {
//@ public model boolean is_playing;


  /**creating the clip that doesn't change.*/
  private transient Clip my_clip;

  /**taking in the actual music file to the variable wavfile.*/
  private final transient File my_wavfile =
    new File("../../../media/Thrust_music.wav");

  /**initialising stream.*/
  private AudioInputStream my_stream;


  /** Constructor, sets up audio stream. */
  public void music() {
    try {
      my_stream = AudioSystem.getAudioInputStream(my_wavfile);
      // specify what kind of line we want to create
      final DataLine.Info info =
        new DataLine.Info(Clip.class, my_stream.getFormat());
      my_clip = (Clip) AudioSystem.getLine(info);
      my_clip.open(my_stream);
    } catch (LineUnavailableException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    } catch (UnsupportedAudioFileException e1) { e1.printStackTrace();   }
  }


  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public final/*@ pure @*/ boolean playing() {
    //@ assert false;
    return my_clip.isRunning();
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public final void start() {
    //begin playback of the sound clip and loop over and over
    my_clip.loop(Clip.LOOP_CONTINUOUSLY); //@ assert false;
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public final void stop() {
    if (playing()) {
      my_clip.stop();
    }

  }
}
