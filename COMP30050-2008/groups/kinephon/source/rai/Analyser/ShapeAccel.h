#ifndef __INTERPRETER_SHAPEACCEL_H__
#define __INTERPRETER_SHAPEACCEL_H__

#include "../../type.h"
#include "Shape.h"

namespace interpreter
{

/**
 * A shape that compares acceleration plotted against time
 * @author EB
 * @version 1.0
 */
class ShapeAccel : public Shape
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
					(	Track const * const			track,
						ShapeMatches * const		shapeMatches
					);

///////////////////////////////////////////////////////////////////////////////
// friend *tor
//
protected:
					ShapeAccel
					(	sid const					shapeId,
						float const * const			data,
						uint const					width,
						uint const					nData,
						bool const					zoneAnyStart,
						bool const					zoneReverse,
						Zone const * const * const	zones,
						uint const					nZones
					);

};

///////////////////////////////////////////////////////////////////////////////

inline ShapeAccel::ShapeAccel
(	sid const					shapeId,
	float const * const			data,
	uint const					width,
	uint const					nData,
	bool const					zoneAnyStart,
	bool const					zoneReverse,
	Zone const * const * const	zones,
	uint const					nZones
) :	Shape
	(	shapeId,
		data,
		width,
		nData,
		zoneAnyStart,
		zoneReverse,
		zones,
		nZones
	)
{}

}

#endif
