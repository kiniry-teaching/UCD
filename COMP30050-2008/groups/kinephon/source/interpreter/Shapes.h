#ifndef __INTERPRETER_SHAPES_H__
#define __INTERPRETER_SHAPES_H__

#include "Shape.h"

/*
 * Author:	EB
 *
 * Store a collection of shapes and compare an animation against them all
 *	TODO - update this so Shape can contain a Shapes for speed and accel
 *	which means having a separate ShapeLoader rather than a built in one
 *
 */
namespace Interpreter
{

class Shapes
{

public:				// Constructor
					// Load all shape data from file
	/**/			Shapes
					(	char const * const		filename
					);
	virtual			~Shapes						(void);

public:				// Methods
					// Comare an animation against all shapes and return the most
					//	likely one, or NULL if none matched
	Shape *			compare
					(	Animation const * const	animation
					)	const;

private:
					// Array of shapes in this collection
	Shape *			_shapes;
					// Elemements in _shapeSpeed
	int				_length;

};

}

#endif
