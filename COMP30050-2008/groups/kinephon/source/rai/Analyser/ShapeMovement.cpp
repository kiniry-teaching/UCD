#include "ShapeMovement.h"

namespace interpreter
{

bool ShapeMovement::compare
(	Track const * const		track,
	ShapeMatches * const	shapeMatches
){	int *					points;

	points = new int[track->length() * 2];
	
	Shape::test
	(	points,
		track->length() * 2,
		shapeMatches
	);

	return false;

}

}
