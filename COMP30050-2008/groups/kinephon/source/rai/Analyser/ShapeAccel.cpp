#include "Math.h"
#include "ShapeAccel.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// compare
//
bool ShapeAccel::compare
(	Track const * const		track,
	ShapeMatches * const	shapeMatches
){	Points					points;
	Frame *					frame;
	uint					index;
	ShapeMatch *			shapeMatch;
	uint					nPoints;

	nPoints = track->length();

	// Need at least three points to calculate an acceleration
	if(nPoints < 3)
		return false;

	points.initialize(nPoints - 1);

	// Store time and speed as co-ordinates
	// Because all calculations are ints, multiply the speed
	//	by 10 to give the acceleration more levels of detail
	for
	(	index = 0,
		frame = track->first();
		frame->next() != 0;
		frame = frame->next(),
		index++
	)	points[index].frame	= index,
		points[index].time	= static_cast<short>(frame->time()
							- track->first()->time()),
		points[index].y		= abs((frame->u() << 1)) * 10
							+ abs((frame->v() << 1)) * 10;

	points.smoothen(6, epoint::Y);

	points.length()--;

	// Calculate acceleration based on smoothed speed
	for(index = 0; index < points.length(); index++)
		points[index].y = points[index + 1].y - points[index].y;

	points.smoothen(3, epoint::Y);

	if(shapeEditHook != 0)
		shapeEditHook(shapeId(), points);

	shapeMatch = Shape::compare
	(	points,
		shapeMatches
	);

	return shapeMatch != 0;

}

}
