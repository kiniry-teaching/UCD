#ifndef __INTERPRETER_SHAPEMOVEMENT_H__
#define __INTERPRETER_SHAPEMOVEMENT_H__

#include "Shapes.h"

/*
 * Author:	EB
 *
 * Compare against an track's movement
 *
 */
namespace interpreter
{

class ShapeMovement : public Shape
{

public:				// Constructor
					// Load the <name>'d shape data 
	/**/			ShapeMovement 
					(	char const * const	name
					) :	Shape(name) {};

public:				// Methods
					// Comare the movements in the track against this shape
	virtual float	compare
					(	Track const * const	track
					)	const;

private:
					// Sub-shapes describing speeds
	Shapes			_shapeSpeed;
					// Sub-shapes describing accelerations
	Shapes			_shapeAcceleration;

};

}

#endif
