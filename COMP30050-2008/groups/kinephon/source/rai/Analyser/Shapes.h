#ifndef __INTERPRETER_SHAPES_H__
#define __INTERPRETER_SHAPES_H__

#include "../../type.h"
#include "../Recorder/Track.h"
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

///////////////////////////////////////////////////////////////////////////////
// friends
//
	/**
	 * Be friends with ShapesLoader so it can modify the shape collection
	 * @author EB
	 * @version 1.0
	 */
	friend			class ShapesLoader;
	/**
	 * Be friends with ShapeMovement so it can delete this object
	 * @author EB
	 * @version 1.0
	 */
	friend			class ShapeMovement;

///////////////////////////////////////////////////////////////////////////////
// commands
//
public:
	/**
	 * Comare a track against all shapes and return the most likely one, or
	 *	0 if none matched
	 * @param track The track to compare against
	 * @param shapeMatches A shape match collection to add any matched shapes.
	 *	This should be preconfigured to specify the filter for the match
	 * @return True if any matches are found, else false
	 * @author EB
	 * @version 1.0
	 * @pre track != 0 && shapeMatches != 0;
	 * @post \result == true ==> shapeMatches.length() > 0;
	 */
	bool			compare
					(	Track const * const		track,
						ShapeMatches * const	shapeMatches
					)	const;

///////////////////////////////////////////////////////////////////////////////
// private commands
//
private:
	/**
	 * Add a shape to the collection
	 * This is called by ShapesLoader
	 * @param shape Pointer to an allocated shape to add
	 * @author EB
	 * @version 1.0
	 * @pre shape != 0;
	 * @pre _shapeIndex < _nShapes;
	 */
	void			operator +=
					(	Shape *					shape
					);

///////////////////////////////////////////////////////////////////////////////
// friend *tor
//
private:
	/**
	 * Construct the shapes collection. This is done by the ShapesLoader
	 * @param length The total number of shapes this collection will ever hold.
	 *	This must be predetermined before adding each shape to this collection
	 * @author EB
	 * @version 1.0
	 */
					Shapes
					(	uint					length
					);
	/**
	 * Destruct the shapes collection. All shapes in the collection will be
	 *	destroyed too
	 * @author EB
	 * @version 1.0
	 */
	virtual			~Shapes						(void);

///////////////////////////////////////////////////////////////////////////////
// fields
//
private:
	/**
	 * Array of shapes held by this collection. Array is created by ShapeLoader
	 * @author EB
	 * @version 1.0
	 */
	Shape *	*		_shapes;
	/**
	 * Length of _shapes array
	 * @author EB
	 * @version 1.0
	 */
	uint			_nShapes;
	/**
	 * Index of next shape to add when += is called
	 * @author EB
	 * @version 1.0
	 */
	uint			_shapeIndex;

};

}

#endif
