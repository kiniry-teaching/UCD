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

	// Need at least two points to calculate an speed
	nPoints = track->length() - 1;

	// Nothing to test, exit
	if(nPoints <= 0)
		return false;

	points = new int[nPoints * 2];

	// Store time and proportional nPoints of vector as co-ordinates
	//	Don't bother get actual nPoints - it will be scaled to fit
	//	the shape's grid anyways
	for
	(	frame = track->first();
		frame->next() != 0;
		frame = frame->next(),
		index += 2
	)	points[index    ]	= frame->time(),
		points[index + 1]	= (frame->u() << 1)
							+ (frame->v() << 1);

	Shape::smooth(points, nPoints * 2, 6);

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
