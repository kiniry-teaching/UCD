#include "ShapeMatch.h"
#include "Shape.h"

namespace interpreter
{

/*extern*/ SHAPE_EDIT_HOOK shapeEditHook = 0;

///////////////////////////////////////////////////////////////////////////////
// test
//
ShapeMatch * Shape::test
(	int const * const		points,
	uint const				nPoints,
	ShapeMatches * const	shapeMatches
){	float					weight;
	ShapeMatch *			shapeMatch		= 0;

	weight = compare(points, nPoints);

	if(weight >= shapeMatches->weight())
		shapeMatch = add(weight, shapeMatches);

	return shapeMatch;

}

///////////////////////////////////////////////////////////////////////////////
// compare
//
float Shape::compare
(	int const * const	points,
	uint const			nPoints
)	const
{

	return 0.0f;

}

///////////////////////////////////////////////////////////////////////////////
// smooth
//
void Shape::smooth
(	int * const	points,
	uint		nPoints,
	uchar const	range,
	uchar const	affect
)	const
{	int *		tempPoints;
	int			index;
	int			result		= 0;

	// There will be no smoothing, just exit
	if(range == 0)
		return;

	// Only use half the points as smooth only affects x or y, not both
	nPoints >>= 1;

	// Create temporary buffer to store smooth points
	tempPoints = new int[nPoints];

	// Calculate the initial smoothing window left and right of the first point
	//  Because there are no points left of the first point, the first point
	//	is used instead (same with the last point and no right points (below))
	for
	(	index = 0;
		index < range && index < nPoints;
		index++
	)	result += points[affect] + points[(index << 1) + affect];

	for(index = 0; index < nPoints; index++)
	{

		// Shift the smoothing opening window across the points
		if(index + range < nPoints)
			result += points[((index + range) << 1) + affect];
		else
			result += points[((nPoints - 1) << 1) + affect];

		// Calculate and store smooth result
		tempPoints[index] = result / ((range << 1) + 1);

		// Shift the smoothing closing window across the points
		if(index - range >= 0)
			result -= points[((index - range) << 1) + affect];
		else
			result -= points[affect];

	}

	// Copy the updated points over the original
	for(index = 0; index < nPoints; index++)
		points[(index << 1) + affect] = tempPoints[index];

	// Deallocate temporary storage
	delete [] tempPoints;

}

///////////////////////////////////////////////////////////////////////////////
// add
//
ShapeMatch * Shape::add
(	float const				weight,
	ShapeMatches * const	shapeMatches
){	ShapeMatch *			shapeMatch;

	shapeMatch = new ShapeMatch(this, weight);

	(*shapeMatches) += shapeMatch;

	return shapeMatch;

}

}
