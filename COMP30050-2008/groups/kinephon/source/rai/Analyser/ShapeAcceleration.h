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

private:			// Constructor
					// Load the <name>'d shape data 
	/**/			ShapeAcceleration 
					(	float const * const	data
					) :	Shape(data) {};

public:				// Methods
					// Comare the acceleration in the track against this shape
	virtual float	compare
					(	Track const * const	track
					)	const;

};

}

#endif
