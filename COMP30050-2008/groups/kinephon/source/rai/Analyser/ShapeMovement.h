#ifndef __INTERPRETER_SHAPEMOVEMENT_H__
#define __INTERPRETER_SHAPEMOVEMENT_H__

#include "../../type.h"
#include "Shape.h"
#include "Shapes.h"

namespace interpreter
{

/**
 * A shape that compares (x, y) movements
 * @author EB
 * @version 1.0
 */
class ShapeMovement : public Shape
{

///////////////////////////////////////////////////////////////////////////////
// friends
//
	/**
	 * Be friends with ShapesLoader so it can modify the shape's data
	 * @author EB
	 * @version 1.0
	 */
	friend			class ShapesLoader;

///////////////////////////////////////////////////////////////////////////////
// commands
//
public:
	virtual bool	compare
					(	Track const * const		track,
						ShapeMatches * const	shapeMatches
					);

///////////////////////////////////////////////////////////////////////////////
// friend *tor
//
protected:
					ShapeMovement
					(	float const * const	data,
						uint const			width,
						uint const			nData,
						Zone const * const	zones,
						uint const			nZones,
						Shapes *			speedShapes,
						Shapes *			accelShapes
					);

///////////////////////////////////////////////////////////////////////////////
// fields
//
private:
	/**
	 * A movement shape contains a sub collection of speed shapes.
	 * This allows a movement to differ based on a speed gensture
	 * @author EB
	 * @version 1.0
	 */
	Shapes *		_speedShapes;
	/**
	 * A movement shape contains a sub collection of acceleration
	 * shapes.
	 * This allows a movement to differ based on an acceleration
	 *	gensture
	 * @author EB
	 * @version 1.0
	 */
	Shapes *		_accelShapes;

};

///////////////////////////////////////////////////////////////////////////////

ShapeMovement::ShapeMovement
(	float const * const	data,
	uint const			width,
	uint const			nData,
	Zone const * const	zones,
	uint const			nZones,
	Shapes *			speedShapes,
	Shapes *			accelShapes
) :	Shape
	(	data,
		width,
		nData,
		zones,
		nZones
	),
	_speedShapes		(speedShapes),
	_accelShapes		(accelShapes)
{}

}

#endif
