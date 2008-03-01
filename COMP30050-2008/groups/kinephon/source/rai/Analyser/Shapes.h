#ifndef __INTERPRETER_SHAPES_H__
#define __INTERPRETER_SHAPES_H__

#include "Shape.h"

/*
 * Author:	EB
 *
 * Store a collection of shapes and compare a track against them all
 *
 */
namespace interpreter
{

class Shapes
{

				// Be friends with ShapeLoader so it can
				//	modify this shapes data during load
	friend		class ShapesLoader;

public:			// Constructor
	/**/		Shapes					(void);
	virtual		~Shapes					(void);

public:			// Methods
				// Comare a track against all shapes and return the most
				//	likely one, or NULL if none matched
	Shape *		compare
				(	Track const * const	track
				)	const;

private:
				// Array of shapes in this collection
	Shape *		_shapes;
				// Elemements in _shapeSpeed
	int			_length;

};

}

#endif
