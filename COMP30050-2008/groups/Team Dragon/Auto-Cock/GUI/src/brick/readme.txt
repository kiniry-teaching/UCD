The UltraSonic Sensor:

We originally used the ultrasonic sensor for finding the current location of the glass. This seemed to work fine
when we were testing it on a table with markers for each drink location but when the base and track were put 
together for some reason the sensor no longer seemed accurate. It would jump from reading the the carrige as being 
a certain distance away to being another. For example using the code bellow we found it would go from reading it as being 27 
units away to suddenly being 42 and then back to around 27 again while both the carrige and sensor were completely stationary.


public class DistanceTest {
	
	public static void main(String[] args) throws Exception {
		UltrasonicSensor sensor = new UltrasonicSensor(SensorPort.S2);
		int distance;

		while(true) {
			LCD.clear();
			Thread.sleep(200);
			distance = sensor.getDistance()
			LCD.drawInt(distance, 1, 1);
			LCD.refresh();
			Thread.sleep(500);
		}
	}	
}


This would mean that when moving to a position the distance sensor would a lot of the time jump like this and the 
carrige would stop either too early or too late. And ofcourse it would mess up the calculations of how much to move
by if it essentially read itself as being at the wrong position to start with.

We considered trying to get an average reading but as in the example above if the carrige is at position 42 and it keeps
jumping to 27 while you would reduce the margin it would still be far off accurate enough to manage to position itself correctly
under the optics.

Eventually we decided to use revolutions and the tachometer to govern movement. The robot also now just stores it's current position
in a variable that it updates every time it moves. I do feel this is a bit of a hack myself but it was necessary in 
order to have the glass moving to the correct place relyably
