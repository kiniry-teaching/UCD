#include "ShapeMovement.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// compare
//
bool ShapeMovement::compare
(	Track const * const		track,
	ShapeMatches * const	shapeMatches
){	int *					points;
	Frame *					frame;
	int						index;
	ShapeMatch *			shapeMatch;
	uint					length;

	// Need at least one point to calculate an movement
	length = track->length();

	// Nothing to test, exit
	if(length <= 0)
		return false;

	points = new int[length * 2];

	// Store x and y as co-ordinates
	for
	(	frame = track->first();
		frame->next() != 0;
		frame = frame->next(),
		index += 2
	)	points[index    ]	= frame->x(),
		points[index + 1]	= frame->y();

	shapeMatch = Shape::test
	(	points,
		length * 2,
		shapeMatches
	);

	delete [] points;

	// Match this shape against it's speed and accel shapes
	if(shapeMatch != 0)
	{

		if(_speedShapes != 0)
			_speedShapes->compare
			(	track,
				shapeMatch->shapeMatches()
			);

		if(_accelShapes != 0)
			_accelShapes->compare
			(	track,
				shapeMatch->shapeMatches()
			);

	}

	return shapeMatch != 0;

}

}
