package thrust.audio;
import java.io.*;


import javax.sound.sampled.*;

/**
 * In-game music.
 * @author Sean Jago, Naomi O'Reilly 
 * @revision Sean Jago, Naomi O' Reilly.
 * @version 11 April 2008 class Music 

 */

public class Music
{
  		
   private boolean is_playing = false;

   public music()throws IOException,UnsupportedAudioFileException;
  
   private final 
AudioInputStream audio = AudioSystem.getAudioInputStream(new File      ("Thrust_music.wav")); 
   private Clip clip;


   final DataLine.Info clip = new DataLine.Info(Clip.class, audio.getFormat());


   Clip.open(audio);

   if( clip != audio.getFormat())
     {
       
	return;
     } 

/**
  * return is_playing
  */
     
     public boolean playing() 
     {
      return is_playing;
     }

/**
  *  Start playing the music.
  */
   
     public void start() 
     {
      clip.start();
     }

  
/**
  *  Stop playing the music.
  */ 
     public void stop() 
     {
      clip.stop();
     }

}
