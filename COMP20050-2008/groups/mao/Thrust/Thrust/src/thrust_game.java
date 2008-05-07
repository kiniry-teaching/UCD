
import java.util.Vector;

import thrust.input.*;
import thrust.display.*;
import thrust.maps.*;



// thrust game thread

class thrust_game implements Runnable 
{
	private int myFramesPerSecond;
	private int myCurrentChar;
	private static InputHandler myInputHandler;
	private thrustMap myMap;
	private Vector myEntities;

	
	//private InputHandler myInputHandler;
	
	public thrust_game(int fps, String map)
	{
	myFramesPerSecond = fps;
	myMap = new thrustMap(map);
	}

	
	
	
	// Main game loop
	public void run()
	{
	
	initFrame();
	
	// Initialise the fist screen the user sees
	
		// Load the high score into frame
	
			// Press any button to start
		
	
		int count = 0;
		while(true)
		{
			while(myInputHandler.gameRunning == true)
			{
				try
				{
				// Frame calculation and interrupt		
				Thread.sleep(1000/myFramesPerSecond);
				//draw frame
				drawFrame();
				count++;
				System.out.println(count);
				}
				catch(Exception e)
				{
				System.out.println(e);
				}
			}
		}
	}
	
	
	private void initFrame()
	{
	gameFrame tempOne = new gameFrame(myMap);
	myInputHandler = tempOne.myInputHandler;
	}

	
	private void drawFrame()
	{
	
	
	
	}
	
	
}