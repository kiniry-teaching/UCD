#ifndef __INTERPRETER_SHAPESPEED_H__
#define __INTERPRETER_SHAPESPEED_H__

#include "Shape.h"

/*
 * Author:	EB
 *
 * Compare against an animation's speed
 *
 */
namespace interpreter
{

class ShapeSpeed : public Shape
{

public:				// Constructor
					// Load the <name>'d shape data 
	/**/			ShapeSpeed 
					(	char const * const		name
					) :	Shape(name) {};

public:				// Methods
					// Comare the speed in the animation against this shape
	virtual float	compare
					(	Animation const * const	animation
					)	const;

};

}

#endif
