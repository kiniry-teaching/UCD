#ifndef __INTERPRETER_SHAPESPEED_H__
#define __INTERPRETER_SHAPESPEED_H__

#include "Shape.h"

namespace interpreter
{

class ShapeSpeed : public Shape
{

public:				// Constructor
					// Load the <name>'d shape data 
					ShapeSpeed
					(	float const * const	data
					) :	Shape(data) {};

public:				// Methods
					// Comare the speed in the track against this shape
	virtual float	compare
					(	Track const * const	track
					)	const;

};

}

#endif
