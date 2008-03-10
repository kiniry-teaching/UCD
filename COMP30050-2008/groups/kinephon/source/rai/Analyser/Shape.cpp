#include "shapematch.h"
#include "shape.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// test
//
void Shape::test
(	int const * const		points,
	uint const				length,
	ShapeMatches * const	shapeMatches
){	float					weight;

	weight = compare(points, length);

	if(weight >= shapeMatches->weight())
		add(weight, shapeMatches);

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
void Shape::add
(	float const				weight,
	ShapeMatches * const	shapeMatches
){	ShapeMatch *			shapeMatch;

	shapeMatch = new ShapeMatch(this, weight, 0);

	(*shapeMatches) += shapeMatch;

}

}
