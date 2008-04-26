#include "Blimp2.h"
#include "linklist.h"
#include <math.h>

Blimp2::Blimp2()
{
}//get GPS Data 
float Blimp2::readDesX(){
	
}
float Blimp2::readDesY(){

}
float Blimp2::readDesZ(){
  
}
float Blimp2::getCurrX(){
	
}

float Blimp2::getCurrY(){

}
float Blimp2::getCurrZ(){

}

float Blimp2::getVelocityx(){
	 return currX-(past.getX());
}

float Blimp2::getVelocityy(){
	
	return currY-(past.getY());
}
float Blimp2::getDistance(float x,float y,float x1,float y1){
	return fabs(sqrt(pow(((x+x1)/2),2) + pow(((y+y1)/2),2)));
}


void Blimp2::Navigate(){
	if (getDistance(getCurrX(), getCurrY(), desX, desY) > radius){ 
		
	  //Turn on Cervor motors here
	  float result,upperAngle;
      float lenghtoflineA,lenghtoflineB,lenghtoflineC;
      lenghtoflineA = sqrt(pow((past.getX()-readDesX()),2)+pow((past.getY()-readDesY()),2));
      lenghtoflineB = sqrt(pow((readDesX()-getCurrX()),2)+pow((readDesX()-getCurrX()),2));
      lenghtoflineC = sqrt(pow((past.getX()-getCurrX()),2)+pow((past.getY()-getCurrY()),2));
      float A= (pow((lenghtoflineB),2))+(pow((lenghtoflineC),2))-(pow((lenghtoflineA),2));
      float B= 2*(lenghtoflineB*lenghtoflineC);
      float C = (A/B);
      result = acos (C);
      upperAngle= (180 - result);
      if(cos (upperAngle  = 1)){
    	  //SM_FOWARD = ON;
    	  //RUDDER = SETDEGREE(90);
    	  
      }
      if(cos (upperAngle  = -1)){
    	  //SM_FOWARD = ON;
    	  //RUDDER = SETDEGREES(45);//LEFT
      }
      if(sin (upperAngle  > 1)){
    	 // SM_FOWARD = ON;
    	  //RUDDER = SETDEGREES(135);//RIGHT
      }
      if(sin (upperAngle  < 1)){
    	 //SM_FOWARD = ON;
    	//  RUDDER = SETDEGREES(45);//LEFT
      }
	}
	
      
}

Blimp2::~Blimp2()
{
}
