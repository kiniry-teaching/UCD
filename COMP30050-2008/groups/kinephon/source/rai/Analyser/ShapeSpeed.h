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

public:
					ShapeSpeed
					(	float const * const	data,
						uint const			width,
						uint const			nData,
						Zone const * const	zones,
						uint const			nZones
					) :	Shape
						(	data,
							width,
							nData,
							zones,
							nZones
						) {};

public:
	virtual bool	compare
					(	Track const * const		track,
						ShapeMatches * const	shapeMatches
					)	const;

};

}

#endif
