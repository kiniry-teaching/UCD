#ifndef __INTERPRETER_SHAPES_H__
#define __INTERPRETER_SHAPES_H__

#include "Shape.h"

namespace interpreter
{

/**
 * Collection of shapes to compare against each Track
 * @author EB
 * @version 1.0
 */
class Shapes
{

	/**
	 * Be friends with ShapesLoader so it can modify the shape collection
	 * @author EB
	 * @version 1.0
	 */
	friend		class ShapesLoader;

private:
	/**
	 * Construct the shapes collection. This is done by the ShapesLoader
	 * @author EB
	 * @version 1.0
	 */
				Shapes
				(	uint				length
				);
	/**
	 * Destruct the shapes collection. All shapes in the collection will be
	 *	destroyed too
	 * @author EB
	 * @version 1.0
	 */
	virtual		~Shapes					(void);

public:
	/**
	 * Comare a track against all shapes and return the most likely one, or
	 *	0 if none matched
	 * @param track The track to compare against
	 * @return The nearest matching shape within range, or 0 if no near
	 *	matches are found
	 * @author EB
	 * @version 1.0
	 */
	Shape *		compare
				(	Track const * const	track
				)	const;

private:
	/**
	 * Add a shape to the collection by index.
	 * This is called by ShapesLoader
	 * @param index The index to store this shape at. Must be unique for each
	 *	shape or existing ones will be overwritten
	 * @param shape Pointer to an allocated shape
	 * @author EB
	 * @version 1.0
	 * @pre index >= 0 && index <= _length;
	 * @pre shape != 0;
	 */
	void		loadShape
				(	uint				index,
					Shape *				shape
				);

private:
	/**
	 * Array of shapes held by this collection. Array is created by ShapeLoader
	 * @author EB
	 * @version 1.0
	 */
	Shape *		_shapes;
	/**
	 * Length of _shapes array
	 * @author EB
	 * @version 1.0
	 */
	uint		_nShapes;

};

}

#endif
