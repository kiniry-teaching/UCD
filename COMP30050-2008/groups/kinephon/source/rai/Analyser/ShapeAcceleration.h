#ifndef __INTERPRETER_SHAPEACCEL_H__
#define __INTERPRETER_SHAPEACCEL_H__

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

private:
					ShapeAccel 
					(	float const * const		data,
						uint const				width,
						uint const				nData,
						Zone const * const		zones,
						uint const				nZones
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
