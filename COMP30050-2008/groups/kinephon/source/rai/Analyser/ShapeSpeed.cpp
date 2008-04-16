#include "ShapeSpeed.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// compare
//
bool ShapeSpeed::compare
(	Track const * const		track,
	ShapeMatches * const	shapeMatches
){	int *					points;
	Frame *					frame;
	int						index;
	ShapeMatch *			shapeMatch;
	uint					nPoints;

	nPoints = track->length();

	// Need at least two points to calculate an speed
	if(nPoints < 2)
		return false;

	nPoints = (nPoints - 1) << 1;
	points = new int[nPoints];

	// Store time and proportional nPoints of vector as co-ordinates
	//	Don't bother get actual nPoints - it will be scaled to fit
	//	the shape's grid anyways
	for
	(	index = 0,
		frame = track->first();
		frame->next() != 0;
		frame = frame->next(),
		index += 2
	)	points[index    ]	= frame->time(),
		points[index + 1]	= abs((frame->u() << 1))
							+ abs((frame->v() << 1));

	Shape::smooth(points, nPoints, 6, 1);

	if(shapeEditHook != 0)
		shapeEditHook(shapeId(), points, nPoints);

	shapeMatch = Shape::test
	(	points,
		nPoints,
		shapeMatches
	);

	delete [] points;

	return shapeMatch != 0;

}

}
