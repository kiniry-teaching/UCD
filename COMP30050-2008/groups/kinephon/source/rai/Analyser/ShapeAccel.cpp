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

	// Need at least three points to calculate an acceleration
	nPoints = track->length() - 2;

	// Nothing to test, exit
	if(nPoints <= 0)
		return false;

	points = new int[nPoints * 2];

	// Store time and speed as co-ordinates
	for
	(	frame = track->first();
		frame->next() != 0;
		frame = frame->next(),
		index += 2
	)	points[index    ]	= frame->time(),
		points[index + 1]	= (frame->u() << 1)
							+ (frame->v() << 1);

	if(shapeEditHook != 0)
		shapeEditHook(points, nPoints * 2);

	shapeMatch = Shape::test
	(	points,
		nPoints * 2,
		shapeMatches
	);

	delete [] points;

	return shapeMatch != 0;

}

}
