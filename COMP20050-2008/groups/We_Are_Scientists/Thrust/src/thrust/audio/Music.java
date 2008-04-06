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
  public static void main(String[] args) throws Exception {

    
    File soundFile = new File("Thrust_music.mp3");
    AudioInputStream sound = AudioSystem.getAudioInputStream(soundFile);

    DataLine.Info info = new DataLine.Info(Clip.class, sound.getFormat());
    Clip clip = (Clip) AudioSystem.getLine(info);
    clip.open(sound);


    while(menu = true)
    { clip.loop(Clip.LOOP_CONTINUOUSLY);}
  }
public static boolean menu =false;
boolean is_playing;
  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {
    return true;
    
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    menu = true;
   
  
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    menu = false; //@ assert false;
  }
}
