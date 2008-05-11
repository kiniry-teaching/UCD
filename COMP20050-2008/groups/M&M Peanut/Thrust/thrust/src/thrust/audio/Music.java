/**
 * @author Sean Jago, Naomi O' Reilly
 * @revised Sean Jago, Naomi O' Reilly
 */
package thrust.audio;


import java.io.*;

import javax.sound.sampled.*;

public class Music{


private boolean is_playing = false;


AudioInputStream audio = AudioSystem.getAudioInputStream(new File("Thrust_music.wav"));
private Clip clip;
DataLine.Info clip = new DataLine.Info(Clip.class, audio.getFormat());

    if(!AudioSystem.isLineSupported(clip))
    {
	return;
    }

	Clip clip = (Clip) AudioSystem.getLine(audio);

 //@ public model boolean i)s_playing;
    
 /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {
   
    return is_playing;
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
  
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop()
  {
   
   
    
  }
}
