#include "Math.h"
#include "ShapeSpeed.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// compare
//
bool ShapeSpeed::compare
(	Track const * const		track,
	ShapeMatches * const	shapeMatches
){	Points					points;
	Frame *					frame;
	uint					index;
	ShapeMatch *			shapeMatch;
	uint					nPoints;

	nPoints = track->length();

	// Need at least two points to calculate an speed
	if(nPoints < 2)
		return false;

	nPoints--;
	points.initialize(nPoints);

	// Store time and proportional nPoints of vector as co-ordinates
	//	Don't bother get actual nPoints - it will be scaled to fit
	//	the shape's grid anyways
	for
	(	index = 0,
		frame = track->first();
		frame->next() != 0;
		frame = frame->next(),
		index++
	)	points[index].time	= index,
		points[index].time	= static_cast<short>(frame->time()
							- track->first()->time()),
		points[index].y		= abs((frame->u() << 1))
							+ abs((frame->v() << 1));

	points.smoothen(6, epoint::Y);

	if(shapeEditHook != 0)
		shapeEditHook(shapeId(), points);

	shapeMatch = Shape::compare
	(	points,
		shapeMatches
	);

	return shapeMatch != 0;

}

}
