#ifndef MOVEMENT_H_
#define MOVEMENT_H_

/*
 * Autor: Sumbo
 * The movement of the gesture/track
 * Depending on the different control of the music we have??
 * The motion that response to the shape in general
 * It works with the track class 
 * 
 */

class Movement
{
public:	
		//The Constructor for the movement
		Movement();
		
		//The deconstructor for the movement		
		virtual ~Movement();

               //the main work of the interpreter converting the movement into commads
              // return integer of the last frame(point) use.
             int tracking(Track* track);
		
};

#endif /*MOVEMENT_H_*/
