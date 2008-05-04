package thrust.display;

import java.awt.Frame;
import java.awt.TextArea;
import java.awt.Dimension;
import java.awt.Point;

import thrust.maps.thrustMap;

public class gameFrame extends Frame
{

	private TextArea myMapArea;
	private Frame myHighScoreFrame;
	private TextArea myHighScoreArea;

	public gameFrame(thrustMap map)
	{	
	
		try
		{
		// Create fame and add text area to it
		this.setTitle("Thrust Game");
		this.setSize(400,400);
		this.setResizable(false);
		//this.addKeyListener(new InputHandler);
		
		// Create text area for drawing
		myMapArea = new TextArea("", 0, 0, 3);
		myMapArea.insert(map.myMapSection.mySectionDetails, 0);
		myMapArea.setEditable(false);
		// add map text area to frame
		this.add(myMapArea);
	
		// Create high score text area
		myHighScoreArea = new TextArea("",0,0,3);
		myHighScoreArea.insert(map.myHighScore.mySectionDetails, 0);
		myHighScoreArea.setEditable(false);
		
		// Create high score area
		myHighScoreFrame = new Frame("High Score");
		myHighScoreFrame.setBounds(180, 200, 200, 200);
		myHighScoreFrame.setResizable(false);
		
	
		
	
		
	
		
		
		
		
		
		}
		catch(Exception e)
		{
		System.out.println(e);
		}
	}
	
	
		
}