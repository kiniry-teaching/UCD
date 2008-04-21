#include "Math.h"
#include "Points.h"
#include "ShapeMovement.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// compare
//
bool ShapeMovement::compare
(	Track const * const		track,
	ShapeMatches * const	shapeMatches
){	Points					points;
	Frame *					frame;
	uint					index;
	ShapeMatch *			shapeMatch;
	uint					nPoints;
	ShapeMatches *			subShapeMatches;

	nPoints = track->length();

	// Need at least one point to calculate a movement
	if(nPoints < 1)
		return false;

	points.initialize(nPoints);

	// Store x and y as co-ordinates
	for
	(	index = 0,
		frame = track->first();
		frame != 0;
		frame = frame->next(),
		index++
	)	points[index].frame	= index,
		points[index].x		= frame->x(),
		points[index].y		= frame->y();

	// Smooth the x and y coordinates
	points.smoothen(2, epoint::X);
	points.smoothen(2, epoint::Y);
	points.sharpen(static_cast<float>(20.0f * Math::PI() / 180));

	if(shapeEditHook != 0)
		shapeEditHook(shapeId(), points);

	shapeMatch = Shape::compare
	(	points,
		shapeMatches
	);

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
