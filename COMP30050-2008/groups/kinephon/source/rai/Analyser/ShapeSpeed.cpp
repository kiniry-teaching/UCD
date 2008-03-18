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
	uint					length;

	// Need at least two points to calculate an speed
	length = track->length() - 1;

	// Nothing to test, exit
	if(length <= 0)
		return false;

	points = new int[length * 2];

	// Store time and proportional length of vector as co-ordinates
	//	Don't bother get actual length - it will be scaled to fit
	//	the shape's grid anyways
	for
	(	frame = track->first();
		frame->next() != 0;
		frame = frame->next(),
		index += 2
	)	points[index    ]	= frame->time(),
		points[index + 1]	= (frame->u() << 1)
							+ (frame->v() << 1);

	shapeMatch = Shape::test
	(	points,
		length * 2,
		shapeMatches
	);

	delete [] points;

	return shapeMatch != 0;

}

}
