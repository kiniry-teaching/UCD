#ifndef __INTERPRETER_SHAPESPEED_H__
#define __INTERPRETER_SHAPESPEED_H__

#include "../../type.h"
#include "Shape.h"

namespace interpreter
{

/**
 * A shape that compares speed plotted against time
 * @author EB
 * @version 1.0
 */
class ShapeSpeed : public Shape
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
					ShapeSpeed
					(	sid const				shapeId,
						float const * const		data,
						uint const				width,
						uint const				nData,
						bool const				zoneAnyStart,
						bool const				zoneReverse,
						Zone const * const		zones,
						uint const				nZones
					);

};

///////////////////////////////////////////////////////////////////////////////

inline ShapeSpeed::ShapeSpeed
(	sid const			shapeId,
	float const * const	data,
	uint const			width,
	uint const			nData,
	bool const			zoneAnyStart,
	bool const			zoneReverse,
	Zone const * const	zones,
	uint const			nZones
) :	Shape
	(	shapeId,
		data,
		width,
		nData,
		zoneAnyStart,
		zoneReverse,
		zones,
		nZones
	) {}

}

#endif
