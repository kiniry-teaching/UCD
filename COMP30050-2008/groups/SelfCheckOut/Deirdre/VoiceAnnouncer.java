package selfCheckOut;
import database.Item;
import sun.audio.*;
import java.io.*;
import java.util.LinkedList;
/**@author deirdrepower
  **/
public class VoiceAnnouncer {

private static String sound;
private static String playsound;




private static LinkedList<String> soundList = new LinkedList<String>();
private static String playName =  "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/appleVoice.wav";
private static String playName1 = "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/appleVoice.wav";
private static String playName2 = "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/appleVoice.wav";
private static String orangejuice = "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/orangejuice.wav";
private static String toothpaste = "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/toothpaste.wav";
private static String milk =  "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/orangejuice.wav";
private static String locozade = "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/lucozade.wav";
private static String notebook = "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/notebook.wav";

public VoiceAnnouncer(){

	soundList.add(playName);
	soundList.add(playName1);
	soundList.add(playName2);
}

public static void VoicePlayer(Item aProduct) throws Exception{
	//fileName = getFile(aProduct);
	sound = aProduct.name;
	findVoice();
	
}

	
public static void findVoice() throws IOException{	
	for(int i = 0; i<soundList.size(); i++)
	{
		if(soundList.get(i) == sound)
		{
			playVoice(soundList.get(i));
		}
		
	}
}


public static void playBeep() throws IOException{
	InputStream in = new FileInputStream("/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/appleVoice.wav");
	AudioStream as = new AudioStream(in);
	AudioPlayer.player.start(as);
}


public static void playVoice(String asound) throws IOException{
	InputStream in = new FileInputStream(asound);
	AudioStream as = new AudioStream(in);
	AudioPlayer.player.start(as);
}


}
