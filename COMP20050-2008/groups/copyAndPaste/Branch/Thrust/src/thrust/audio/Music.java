package thrust.audio;
             
  
 import java.io.File; 
 import java.io.IOException; 
  
 import javax.sound.sampled.LineUnavailableException; 
 import javax.sound.sampled.UnsupportedAudioFileException;
 import javax.sound.sampled.AudioFormat; 
 import javax.sound.sampled.AudioInputStream; 
 import javax.sound.sampled.AudioSystem; 
 import javax.sound.sampled.Clip; 
 import javax.sound.sampled.DataLine; 
  
  
 
 public class Music { 
   
  
    
   private final transient File my_musicFile = new File("Thrust_music.wav.wav"); 
   private final transient Clip my_music; 
 
   
   public Music() throws LineUnavailableException, IOException, UnsupportedAudioFileException { 
   
	   final AudioInputStream my_Ais = AudioSystem.getAudioInputStream(my_musicFile); 
	   final AudioFormat af = my_Ais.getFormat(); 
	   final DataLine.Info info = new DataLine.Info(Clip.class, af); 
  
	   my_music = (Clip) AudioSystem.getLine(info); 
	   my_music.open(my_Ais); 
   
   } 
     
   public final boolean isPlaying() { 
	   
	   return my_music.isRunning(); 
   } 
  
   public final void start() { 
	   
	   my_music.loop(Clip.LOOP_CONTINUOUSLY); 
	   
   } 
   
   public final void stop() { 
	   my_music.stop(); 
	   
	   
   } 
   
   
   
 } 
   
   
 
   
  
   
