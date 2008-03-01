#ifndef __INTERPRETER_SHAPEACCELERATION_H__
#define __INTERPRETER_SHAPEACCELERATION_H__

#include "Shape.h"

/*
 * Author:	EB
 *
 * Compare against a track's acceleration
 *
 */
namespace interpreter
{

class ShapeAcceleration : public Shape
{

public:				// Constructor
					// Load the <name>'d shape data 
	/**/			ShapeAcceleration 
					(	char const * const	name
					) :	Shape(name) {};

public:				// Methods
					// Comare the acceleration in the track against this shape
	virtual float	compare
					(	Track const * const	track
					)	const;

};

}

#endif
