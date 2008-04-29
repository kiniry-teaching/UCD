SelfCheckOut Project

Classes to test other classes are located in /selfCheckOut/testCode

The Scales is read through a Phidget and data is sent over the network using ScalesServer.  
The Phidget needs to be correctly installed for this to work

The barcodes are scanned from a picture in ProcessHardWare,  it is necessary that the 
Java Media Framework is installed for this to work correctly and that the JMF registry be able to read the camera
and that the JMF registry camera ID be hardcoded into the CameraCapture.java file


For the recent demo we used a trimmed down version of the code as we did not have the equipment to adjust the 
variable resistors to emulate scales .  This slimmed down version is SCO and it is necessary that mySQL is 
working correctly for this program to run and that ScalesServer and that ProcessHardWare are both running. The full featured version is called Main.






