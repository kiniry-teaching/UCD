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
	uint const				length,
	ShapeMatches * const	shapeMatches
){	float					weight;
	ShapeMatch *			shapeMatch		= 0;

	weight = compare(points, length);

	if(weight >= shapeMatches->weight())
		shapeMatch = add(weight, shapeMatches);

	return shapeMatch;

}

///////////////////////////////////////////////////////////////////////////////
// compare
//
float Shape::compare
(	int const * const	points,
	uint const			length
)	const
{

	return 0.0f;

}

///////////////////////////////////////////////////////////////////////////////
// smooth
//
void Shape::smooth
(	int * const	points,
	uint const	length,
	uint const	range
)	const
{	int *		tempPoints;
	uint		index;
	uint		startIndex;
	uint		endIndex;
	int			result;

	// There will be no smoothing, just exit
	if(range == 0)
		return;

	// Create temporary buffer to store smooth points
	tempPoints = new int[length];

	// Calculate the first few points used for smoothing
	for
	(	endIndex = 0;
		endIndex < range && endIndex < length;
		endIndex++
	)	result += points[endIndex];

	for(index = 0; index < length; index++)
	{

		// Calculate smooth result
		points[index] = result / (endIndex - startIndex);

		// Shift the smoothing window across the points
		if(index >= range)
		{	result -= points[startIndex];
			startIndex++;
		}

		if(endIndex < length)
		{	endIndex++;
			result += points[endIndex];
		}

	}

	// Copy the updated points over the original
	memcpy(points, tempPoints, length >> 1);

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
