package thrust.audio;



import javax.sound.sampled.*;
import java.io.File;

public class Music {
//@ public model boolean is_playing;

  /** File for music. */

  private transient Clip clip;
  private final transient File wavfile = new File("../../../media/Thrust_music.wav");
  private AudioInputStream stream = null;


  /** Constructor, sets up audio stream. */
  public Music() {
    try {
      stream = AudioSystem.getAudioInputStream(wavfile);

      //AudioFormat format = stream.getFormat(); 
    } catch (Exception e) {
      e.fillInStackTrace();
    }
    // specify what kind of line we want to create 
    final DataLine.Info info = new DataLine.Info(Clip.class, stream.getFormat());
    
    try {
      // create the line
      clip = (Clip) AudioSystem.getLine(info);
      // load the samples from the stream 
      clip.open(stream);
      
    } catch (Exception e) {
      e.fillInStackTrace();
    }
  }


  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public final/*@ pure @*/ boolean playing() {
    //@ assert false;
    return clip.isRunning();
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public final void start() {
  //begin playback of the sound clip and loop over and over
    clip.loop(Clip.LOOP_CONTINUOUSLY); //@ assert false;
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public final void stop() {
    if(playing())
      clip.stop();
    
    
  }
}