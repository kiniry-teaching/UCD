package thrust.audio;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
import java.io.File;
/**
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music  {
  //@ public model boolean is_playing;
  /**
   * In-game music.
   * @ the clip
   * @
   */
  private transient Clip clip;
  /**
   * In-game music.
   * @ the soundfile java.io input
   * @
   */
  private final transient File soundFile = new File("Thrust_music.wav");
  /**
   * In-game music.
   * @Music method loads clips
   * @
   */
  public Music() {
    try {
    //File soundFile = new File("Thrust_music.mp3");
    AudioInputStream sound = AudioSystem.getAudioInputStream(soundFile);

    DataLine.Info info = new DataLine.Info(Clip.class, sound.getFormat());
    Clip clip = (Clip) AudioSystem.getLine(info);
    clip.open(sound);
    } catch (Exception e) {
     System.out.println("error");
    }


  }

  /**
   * In-game music.
   * @boolean to tell when music is playing
   * @true or false
   */
private boolean isplaying;
  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public final /*@ pure @*/ boolean playing() {
    isplaying = true;
    return clip.isRunning();

  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public final void start() {
    clip.start();
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public final void stop() {
    clip.stop();
    //@ assert false;
  }
}
