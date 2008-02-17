#ifndef __INTERPRETER_SHAPEACCELERATION_H__
#define __INTERPRETER_SHAPEACCELERATION_H__

#include "Shape.h"

/*
 * Author:	EB
 *
 * Compare against an animation's acceleration
 *
 */
namespace Interpreter
{

class ShapeAcceleration : public Shape
{

public:				// Constructor
					// Load the <name>'d shape data 
	/**/			ShapeAcceleration 
					(	char const * const		name
					) :	Shape(name) {};

public:				// Methods
					// Comare the acceleration in the animation against this shape
	virtual float	compare
					(	Animation const * const	animation
					)	const;

};

}

#endif
