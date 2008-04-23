package selfCheckOut;
import java.applet.*;
import java.awt.List;
import database.Product;
import sun.audio.*;
import java.io.*;
import java.util.LinkedList;
import database.ItemQuery;
import database.Product;

/**@author deirdrepower
  **/
public class VoiceAnnouncer {
/*TODO: Store all the voices*/
private static String fileName;
//private static String playName;
private static String playBeep;


private static LinkedList<String> soundList = new LinkedList<String>();
private static String playName =  "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/appleVoice.wav";
private static String playName1 = "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/appleVoice.wav";
private static String playName2 = "/Users/deirdrepower/workspace3/selfCheckOut/dpower/src/appleVoice.wav";

public VoiceAnnouncer(){

	soundList.add(playName);
	soundList.add(playName1);
	soundList.add(playName2);
}

public static void VoicePlayer(Product aProduct){
	//fileName = getFile(aProduct);
	fileName = aProduct.name;
	findVoice();
	
}

	
public static void findVoice() throws IOException{	
	for(int i = 0; i<soundList.size(); i++)
	{
		if(soundList.get(i) == fileName)
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


public static void playVoice(String fileToName) throws IOException{
	InputStream in = new FileInputStream(fileToName);
	AudioStream as = new AudioStream(in);
	AudioPlayer.player.start(as);
}


}
