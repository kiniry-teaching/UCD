#ifndef MOVEMENT_H_
#define MOVEMENT_H_

/*
 * Autor: Sumbo
 * The motion that response to the shape in general
 * It works with the animation class 
 */

class Movement
{
public:	
		//The Constructor for the movement
		Movement();
		
		//The deconstructor for the movement		
		virtual ~Movement();
		
		//For the whole shape to be move at once
		void moveShape();
};

#endif /*MOVEMENT_H_*/
