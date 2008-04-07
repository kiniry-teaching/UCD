package thrust.audio;
import javax.sound.sampled.*;
import java.io.File;
/**
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music  {
  //@ public model boolean is_playing;
  private transient Clip clip;
  //public static void main(String[] args) throws Exception {
  private final transient File soundFile = new File("Thrust_music.wav");
  
  public Music() {
    try{
    
    //File soundFile = new File("Thrust_music.mp3");
    AudioInputStream sound = AudioSystem.getAudioInputStream(soundFile);

    DataLine.Info info = new DataLine.Info(Clip.class, sound.getFormat());
   
    Clip clip = (Clip) AudioSystem.getLine(info);
    clip.open(sound);
    }catch(Exception e){System.out.println("error");}


  
  }

boolean is_playing;
  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public final /*@ pure @*/ boolean playing() {
    return clip.isRunning();
    
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    clip.start();
   
  
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    clip.stop();
    //@ assert false;
  }
}
