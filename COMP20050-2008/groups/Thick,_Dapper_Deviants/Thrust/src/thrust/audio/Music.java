package thrust.audio;
import java.io.*;
import javax.sound.sampled.*;


/**
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music {
  public Clip clip;
  private AudioFormat format;
  private AudioInputStream in;
  public int loopCount;
  //@ public model boolean is_playing;

  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {
    return clip.isRunning();
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
      try{
        in = AudioSystem.getAudioInputStream(new File("./media/Thrust_music.wav"));
        format = in.getFormat();
        DataLine.Info info = new DataLine.Info(Clip.class, format);
        clip = (Clip)AudioSystem.getLine(info);
        clip.open(in);
        clip.loop(clip.LOOP_CONTINUOUSLY); 
          
      }catch(Exception ex){
        ex.printStackTrace();
      }
  }
  public void prepare audio
      public void stop(){ 
        clip.stop();
      }
      public static void main(String[] args){
        while(true);
      }
}
