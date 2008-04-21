package brick;

import rcv.*;

import lejos.nxt.LCD;
import lejos.nxt.Motor;
import lejos.nxt.SensorPort;
import lejos.nxt.TouchSensor;
import lejos.nxt.UltrasonicSensor;

public class Robot {

	public static void main(String[] args) {		
		byte [] positions = new byte[10];
		boolean stir = false;
		boolean ice = false;

		while(true){
			execute(positions, stir, ice);
		}
	}
	
	public static void execute(byte[] positions, boolean stir, boolean ice){
		//need to talk with the group about how we're doing some this so it's just a rough idea atm
		for(int i = 0; i < positions.length; i++){
			if(positions[i] == 1){
				reset();
			}else if(positions[i] == 2){
				moveTo(positions[i]);
				if(stir){
					stir();
				}
				if(ice){
					//get ice, haven't written that yet
				}
			}else{
				moveTo(positions[i]);
				raiseGlass();
				//wait while drink fills
				try { Thread.sleep(3000); }
				catch (InterruptedException e) { }
				lowerGlass();
			}
		}

	}
	
	public static void reset(){
		TouchSensor touch = new TouchSensor(SensorPort.S1);
		Motor.A.setSpeed(200);
		Motor.A.forward();
		while(!touch.isPressed()){
		}
		Motor.A.stop();
		LCD.clear();
		LCD.drawString("Reset!",0,1);
		LCD.refresh();
	}
	
	public static byte getPosition(){
		int dist = getDistance();
		byte position = distanceToPos(dist);
		return position;
	}
	
	
	public static int getDistance(){
		UltrasonicSensor sensor = new UltrasonicSensor(SensorPort.S2);
		int distance = sensor.getDistance();
		while(distance == 255){
			distance = sensor.getDistance();
		}
		LCD.clear();
		LCD.drawString("The distance is:",0,1);
		LCD.drawInt(distance,0,2);
		LCD.refresh();
		return distance;
	}
	
	// haven't yet decided whether I have a check here that works out the current position before moving or if I should put in another method for that
	public static void moveTo(byte position){
		UltrasonicSensor sensor = new UltrasonicSensor(SensorPort.S2);
		int distance = posToDistance(position);		
		Motor.A.setSpeed(200);
		Motor.A.backward();
		while(sensor.getDistance() != distance){
		}
		Motor.A.stop();
	}
	
	public static void raiseGlass(){
		LCD.clear();
		LCD.drawString("Raising...", 0, 1);
		LCD.refresh();
		Motor.C.rotate(375);		
		LCD.clear();
	}
	
	public static void lowerGlass(){	
		LCD.clear();
		LCD.drawString("Lowering", 0, 1);
		LCD.refresh();
		Motor.C.rotate(-375);
		LCD.clear();
	}
	
	public static void stir(){
		raiseGlass();
		Motor.B.setSpeed(2500);
		LCD.drawString("Stirring...", 0, 1);
		LCD.refresh();
		Motor.B.forward();
		try { Thread.sleep(7000); }
		catch (InterruptedException e) { }
		Motor.B.stop();
		lowerGlass();
	}
	
	public static int posToDistance(byte pos){
		switch(pos){
			case 1: return 0;
			case 2: return 15;
			case 3: return 30;
			case 4: return 45;
			case 5: return 60;
		}
		//returns zero if the position is found (mostly just to keep the compiler happy)
		return 0;
	}
	
	// we may need to rework this as I'm not sure how accurate the distances will be
	public static byte distanceToPos(int dist){
		switch(dist){
			case 0: byte a = 1; return a;
			case 15: byte b = 2; return b;
			case 30: byte c = 3; return c;
			case 45: byte d = 4; return d;
			case 60: byte e = 5; return e;
		}
		//returns zero to keep the compiler happy)
		return 0;
	}
		
	
}