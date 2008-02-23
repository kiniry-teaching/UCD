#ifndef __INTERPRETER_SHAPEMOVEMENT_H__
#define __INTERPRETER_SHAPEMOVEMENT_H__

#include "Shapes.h"

/*
 * Author:	EB
 *
 * Compare against an animation's movement
 *
 */
namespace Interpreter
{

class ShapeMovement : public Shape
{

public:				// Constructor
					// Load the <name>'d shape data 
	/**/			ShapeMovement 
					(	char const * const		name
					) :	Shape(name) {};

public:				// Methods
					// Comare the movements in the animation against this shape
	virtual float	compare
					(	Animation const * const	animation
					)	const;

private:
					// Sub-shapes describing speeds
	Shapes			_shapeSpeed;
					// Sub-shapes describing accelerations
	Shapes			_shapeAcceleration;

};

}

#endif
