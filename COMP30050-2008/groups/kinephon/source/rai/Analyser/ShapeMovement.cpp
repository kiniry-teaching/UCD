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
	uint					nPoints;
	ShapeMatches *			subShapeMatches;

	// Need at least one point to calculate an movement
	nPoints = track->length();

	// Nothing to test, exit
	if(nPoints <= 0)
		return false;

	points = new int[nPoints * 2];

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
		nPoints * 2,
		shapeMatches
	);

	delete [] points;

	// Match this shape against it's speed and accel shapes
	if(shapeMatch != 0)
	{

		// Create a new ShapeMatches to hold the sub-shape's
		//	matches and create it with the same parameters
		//	as the passed in shapeMatches
		subShapeMatches = new ShapeMatches(shapeMatches);

		// If one or more matches are made, by either speed or accel
		//	sub shapes, store the matches as a child of the match
		//	made by this movement
		// If there are no matches, just delete the match object and
		//	leave the child matches as 0
		if(_speedShapes->compare(track, subShapeMatches) == true
		|| _accelShapes->compare(track, subShapeMatches) == true)
			shapeMatch->shapeMatches() = subShapeMatches;
		else
			delete subShapeMatches;

	}

	return shapeMatch != 0;

}

}
