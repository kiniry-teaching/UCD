package thrust.display;

import java.awt.Frame;
import java.awt.TextArea;
import java.awt.Dimension;
import java.awt.Point;

import thrust.maps.thrustMap;
import thrust.input.InputHandler;

public class gameFrame extends Frame
{

	private TextArea myMapArea;
	public InputHandler myInputHandler;

	public gameFrame(thrustMap map)
	{	
	
		try
		{
		// Create fame and add text area to it
		this.setTitle("Thrust Game");
		this.setSize(400,400);
		this.setResizable(false);

		
		// Create text area for drawing
		myMapArea = new TextArea("", 0, 0, 3);
		myMapArea.insert(map.getTransposeHighScore(), 0);
		myMapArea.setEditable(false);
		
		myInputHandler = new InputHandler();
		myMapArea.addKeyListener(myInputHandler);
		// add map text area to frame
		this.add(myMapArea);	
		this.setVisible(true);	
		
		
		
		
		
		}
		catch(Exception e)
		{
		System.out.println(e);
		}
	}

	
	
		
}