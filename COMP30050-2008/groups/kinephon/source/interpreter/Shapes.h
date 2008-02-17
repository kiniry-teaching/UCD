#ifndef __INTERPRETER_SHAPES_H__
#define __INTERPRETER_SHAPES_H__

#include "Shape.h"

/*
 * Author:	EB
 *
 * Store a collection of shapes and compare an animation against them all
 *
 */
namespace Interpreter
{

class Shapes
{

				// Be friends with ShapeLoader so it can
				//	modify this shapes data during load
	friend		class ShapesLoader;

public:			// Constructor
	/**/		Shapes						(void);
	virtual		~Shapes						(void);

public:			// Methods
				// Comare an animation against all shapes and return the most
				//	likely one, or NULL if none matched
	Shape *		compare
				(	Animation const * const	animation
				)	const;

private:
				// Array of shapes in this collection
	Shape *		_shapes;
				// Elemements in _shapeSpeed
	int			_length;

};

}

#endif
