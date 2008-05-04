

import thrust.input.*;
import thrust.display.*;
import thrust.maps.*;
// thrust game thread

class thrust_game extends InputHandler implements Runnable 
{
	private int myFramesPerSecond;
	private int myCurrentChar;
	private InputHandler myInputHandler;
	private thrustMap myMap;

	
	//private InputHandler myInputHandler;
	
	public thrust_game(int fps, String map)
	{
	myFramesPerSecond = fps;
	myMap = new thrustMap(map);
	}

	public void run()
	{
	
	initFrame();
	
	// Initialise the fist screen the user sees
	
		// Load the high score into frame
	
			// Press any button to start
		
	
	
		while(myInputHandler.gameRunning == true)
		{
		
			try
			{
			// Frame calculation and interrupt		
			Thread.sleep(1000/myFramesPerSecond);
			//draw frame
			drawFrame();
			
			}
			catch(Exception e)
			{
			System.out.println(e);
			}
		}
	}
	
	
	private void initFrame()
	{
	gameFrame tempOne = new gameFrame(myMap);
	}

	
	private void drawFrame()
	{
	
	
	}
	
	
}