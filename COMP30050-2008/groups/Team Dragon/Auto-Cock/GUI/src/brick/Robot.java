package brick;

import lejos.nxt.Button;
import lejos.nxt.LCD;
import lejos.nxt.Motor;
import lejos.nxt.SensorPort;
import lejos.nxt.TouchSensor;
import java.lang.Math;
import rcv.*;

/**
 * @author Alistair WIlson
 * 
 */


public class Robot {

	public static void main(String[] args) {
		int [] positions = new int [7];
		BTRObject bt = new BTRObject();

		while(true){
			bt.startServer();
			bt.stopServer();
			positions = bt.getOrder();
			execute(positions);

		}
	}
	
	/** 
	 * Waits for you to press the escape button to signal that the glass is 
	 * in place and you're ready to start. 
	 * Runs through the array of positions moving to each one. If it's the stirrer
	 * or ice dispenser it calls those methods. Positions above 100 were used to
	 * represent nothing, for example not stirring or not adding ice.
	 */
	public static void execute(int[] positions){
		LCD.clear();
		LCD.drawString("Waiting for Glass",0,1);
		LCD.refresh();
		while(!Button.ESCAPE.isPressed()) {
		}
		LCD.clear();
		setCurrentPosition(1);
		for(int i = 0; i < positions.length; i++){
			if(positions[i] == 1){
				moveTo(positions[i]);
				ice();
			}else if(positions[i] == 2){
				moveTo(positions[i]);
				stir();
			}else if (positions[i] > 100){
				
			}else{
				moveTo(positions[i]);
				raiseGlass();
				//wait while drink fills
				try { Thread.sleep(3000); }
				catch (InterruptedException e) { }
				LCD.clear();
				LCD.drawString("Finished", 0, 1);
				LCD.refresh();				
				lowerGlass();
			}
		}
		reset();
	}
	
	/**
	 * Moves back to the starting location by moving backwards 
	 * until it hits the touch sensor
	 */
	public static void reset(){
		TouchSensor touch = new TouchSensor(SensorPort.S1);
		Motor.A.setSpeed(200);
		Motor.A.backward();
		while(!touch.isPressed()){
		}
		Motor.A.stop();
		LCD.clear();
		LCD.drawString("Reset!",0,1);
		LCD.refresh();
	}
	
	/**
	 * Gets the difference between the distances of the current position and the
	 * position it's moving to and then moves by that amount either backwards
	 * or forwards depending on whether the difference was positive or negative
	 * And then sets the current position to the new location.
	 *  
	 * @param position The position to move to
	 */
	public static void moveTo(int position){
		int a = positionToRev(getCurrentPosition());
		int b = positionToRev(position);
		int difference = a - b;
			
		if (position == 1){
			reset();
		}else{
			if(difference > 0){
				Motor.A.rotate(-difference);
			}else if (difference < 0){
				Motor.A.rotate(Math.abs(difference));
			}
		}
		setCurrentPosition(position);
	}
	
	// A varriable used to store the current location of the glass
	public static int currentPosition;
	
	/**
	 * @param position the current location of the glass
	 */
	public static void setCurrentPosition(int position){
		currentPosition = position;
	}

	/**
	 * @return the varriable used for storing where the glass currently is
	 */
	public static int getCurrentPosition(){
		return currentPosition;
	}

	/**
	 * Raises the platform the glass in on
	 */
	public static void raiseGlass(){
		LCD.clear();
		LCD.drawString("Raising...", 0, 1);
		LCD.refresh();
		Motor.C.rotate(200);
		LCD.clear();
	}
	
	/**
	 * Lowers the platform the glass in on
	 */
	public static void lowerGlass(){	
		LCD.clear();
		LCD.drawString("Lowering", 0, 1);
		LCD.refresh();
		Motor.C.rotate(-200);
		LCD.clear();
	}
	
	/**
	 * Raises the glass, rotates the motor attached to the stirrer
	 * and lowers the glass again
	 */
	public static void stir(){
		raiseGlass();
		Motor.B.setSpeed(2500);
		LCD.drawString("Stirring...", 0, 1);
		LCD.refresh();
		Motor.B.forward();
		// Wait while the drink is stirred
		try { Thread.sleep(6000); }
		catch (InterruptedException e) { }
		Motor.B.stop();
		lowerGlass();
		LCD.clear();
	}

	
	/**
	 * Raises the glass to accept the ice. Then Moves gearing from the stirrer
	 * to the ice dispenser and continues rotating enough to release the ice.
	 * After that it will reset the gear to being at the stirrer
	 * And finally lowers the glass again. 
	 */
	public static void ice(){
		raiseGlass();
		Motor.B.setSpeed(2500);
		LCD.drawString("adding ice...", 0, 1);
		LCD.refresh();
		Motor.B.backward();
		// waits the time taken for the gearing to switch and the dispenser
		// to open and then close again
		try { Thread.sleep(8000); }
		catch (InterruptedException e) { }
		
		Motor.B.forward();
		// time taken to reset the gear
		try { Thread.sleep(2000); }
		catch (InterruptedException e) { }
		Motor.B.stop();
		lowerGlass();
		LCD.clear();
	}
	

	/**
	 * Returns the number of revolutions required to move from the reset
	 * location to the given position	
	 *  
	 * @param pos an int that represents one of the possible positions
	 */
	public static int positionToRev(int pos){
		if(pos == 1)
			return 0;
		else if(pos == 2)
			return 475;
		else if(pos == 3)
			return 740;
		else if(pos == 4)
			return 1200;

		return 0;
	}
	
}