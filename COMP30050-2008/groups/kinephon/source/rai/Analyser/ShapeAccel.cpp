#include "ShapeAccel.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// compare
//
bool ShapeAccel::compare
(	Track const * const		track,
	ShapeMatches * const	shapeMatches
){	int *					points;
	Frame *					frame;
	int						index;
	ShapeMatch *			shapeMatch;
	uint					nPoints;

	nPoints = track->length();

	// Need at least three points to calculate an acceleration
	if(nPoints < 3)
		return false;

	nPoints = (nPoints - 1) << 1;
	points = new int[nPoints];

	// Store time and speed as co-ordinates
	// Because all calculations are ints, multiply the speed
	//	by 10 to give the acceleration more levels of detail
	for
	(	index = 0,
		frame = track->first();
		frame->next() != 0;
		frame = frame->next(),
		index += 2
	)	points[index    ]	= frame->time(),
		points[index + 1]	= abs((frame->u() << 1))
							+ abs((frame->v() << 1)) * 10;

	Shape::smooth(points, nPoints, 6, 1);

	nPoints -= 2;

	// Calculate acceleration based on smoothed speed
	for(index = 1; index < nPoints; index += 2)
		points[index] = points[index + 2] - points[index];

	Shape::smooth(points, nPoints, 3, 1);

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
