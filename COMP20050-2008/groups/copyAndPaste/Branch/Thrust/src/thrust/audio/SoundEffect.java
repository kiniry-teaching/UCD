

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
	 /** 
	  * Processes and delegates each keyboard input received. 
	  * @author Joe Kiniry (kiniry@acm.org) 
	  * @version 2 April 2008 
	  * @revised 25/04/08 Ciaran Flynn: 06516564 
	 */ 
	 public class SoundEffect { 
	    
	   private final transient File my_soundFile1 = new File("sound1.wav"); 
	   private final transient File my_soundFile2 = new File("sound2.wav");
	   private final transient File my_soundFile3 = new File("sound3.wav");
	   
	   private final transient Clip my_sound1; 
	   private final transient Clip my_sound2; 
	   private final transient Clip my_sound3; 
	  
	   public Music() throws LineUnavailableException, IOException, UnsupportedAudioFileException { 
	    
		 final AudioInputStream my_Ais1 = AudioSystem.getAudioInputStream(my_soundFile1); 
		 final AudioInputStream my_Ais2 = AudioSystem.getAudioInputStream(my_soundFile2); 
		 final AudioInputStream my_Ais3 = AudioSystem.getAudioInputStream(my_soundFile3); 
		 
	     final AudioFormat af1 = my_Ais1.getFormat(); 
	     final AudioFormat af2 = my_Ais2.getFormat(); 
	     final AudioFormat af3 = my_Ais3.getFormat();
	     
	     final DataLine.Info info1 = new DataLine.Info(Clip.class, af1); 
	     final DataLine.Info info2 = new DataLine.Info(Clip.class, af2); 
	     final DataLine.Info info3 = new DataLine.Info(Clip.class, af3);
	     
	     my_sound1 = (Clip) AudioSystem.getLine(info1); 
	     my_sound2 = (Clip) AudioSystem.getLine(info2); 
	     my_sound3 = (Clip) AudioSystem.getLine(info3); 
	     
	     
	     my_sound1.open(my_Ais1); 
	     my_sound2.open(my_Ais2); 
	     my_sound3.open(my_Ais3); 
	   } 
	   
	   public final boolean isPlaying1() { 
	     return my_sound1.isRunning(); 
	   } 
	   
	   public final boolean isPlaying2() { 
		     return my_sound2.isRunning(); 
		   }
	   
	   public final boolean isPlaying3() { 
		     return my_sound3.isRunning(); 
		   } 
	   
	   
	   public final void startSound1() { 
	     my_sound1.loop(1); 
	   } 
	   
	   public final void startSound2() { 
		     my_sound2.loop(1); 
		   } 
	   
	   public final void startSound3() { 
		     my_sound3.loop(1); 
		   } 
	   
	   public final void stopSound1() { 
	     my_sound1.stop(); 
	   } 
	   
	   public final void stopSound2() { 
		     my_sound2.stop(); 
		   } 
	   public final void stopSound3() { 
		     my_sound3.stop(); 
		   } 
	 } 


