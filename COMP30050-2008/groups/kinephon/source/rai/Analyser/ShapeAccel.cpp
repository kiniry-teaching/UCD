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
	Frame *					frameLast;
	int						index;
	ShapeMatch *			shapeMatch;
	uint					length;

	// Need at least three points to calculate an acceleration
	length = track->length() - 2;

	// Nothing to test, exit
	if(length <= 0)
		return false;

	points = new int[length * 2];

	// Store time and difference-in-speed between
	//	this vector and last vector as co-ordinates
	for
	(	frameLast = track->first(),
		frame = frameLast->next();
		frame->next() != 0;
		frameLast = frame,
		frame = frame->next(),
		index += 2
	)	points[index    ]	= frame->time(),
		points[index + 1]	= (frame->u() << 1)
							+ (frame->v() << 1)
							- (frameLast->u() << 1)
							+ (frameLast->v() << 1);

	shapeMatch = Shape::test
	(	points,
		length * 2,
		shapeMatches
	);

	delete [] points;

	return shapeMatch != 0;

}

}
