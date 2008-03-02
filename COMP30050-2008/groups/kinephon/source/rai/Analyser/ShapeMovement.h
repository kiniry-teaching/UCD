#ifndef __INTERPRETER_SHAPEMOVEMENT_H__
#define __INTERPRETER_SHAPEMOVEMENT_H__

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

public:
					ShapeMovement 
					(	float const * const	data,
						uint const			width,
						uint const			nData,
						Zone const * const	zones,
						uint const			nZones,
						Shapes *			speedShapes,
						Shapes *			accelShapes,
					) :	Shape
						(	data,
							width,
							nData,
							zones,
							nZones
						),
						_speedShapes		(speedShapes),
						_accelShapes		(accelShapes)
						{};

public:
	virtual bool	compare
					(	Track const * const		track,
						ShapeMatches * const	shapeMatches
					)	const;

private:
	/**
	 * A movement shape contains a sub collection of speed shapes.
	 * This allows a movement to differ based on a speed gensture
	 * @author EB
	 * @version 1.0
	 */
	Shapes			_speedShape;
	/**
	 * A movement shape contains a sub collection of acceleration
	 * shapes.
	 * This allows a movement to differ based on an acceleration
	 *	gensture
	 * @author EB
	 * @version 1.0
	 */
	Shapes			_accelShapes;

};

}

#endif
