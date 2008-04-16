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

	nPoints = track->length();

	// Need at least one point to calculate a movement
	if(nPoints < 1)
		return false;

	nPoints <<= 1;
	points = new int[nPoints];

	// Store x and y as co-ordinates
	for
	(	index = 0,
		frame = track->first();
		frame != 0;
		frame = frame->next(),
		index += 2
	)	points[index    ]	= frame->x(),
		points[index + 1]	= frame->y();

	// Smooth the x and y coordinates
	Shape::smooth(points, nPoints, 2, 0);
	Shape::smooth(points, nPoints, 2, 1);

	if(shapeEditHook != 0)
		shapeEditHook(shapeId(), points, nPoints);

	shapeMatch = Shape::test
	(	points,
		nPoints,
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
