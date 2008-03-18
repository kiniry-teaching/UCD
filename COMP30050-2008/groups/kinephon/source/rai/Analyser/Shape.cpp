#include "shapematch.h"
#include "shape.h"

namespace interpreter
{

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
