#include "ShapeMatches.h"
#include <algorithm>
using std::sort;

namespace interpreter
{

bool sortShapeMatches
(	ShapeMatch *	shapeMatchA,
	ShapeMatch *	shapeMatchB
){	return shapeMatchA->weight() > shapeMatchB->weight();
}

///////////////////////////////////////////////////////////////////////////////
// add
//
ShapeMatch * ShapeMatches::add
(	Shape const * const	shape,
	float const			weight,
	float const			angle,
	float const			scale,
	uint const			frame
){	ShapeMatch *		shapeMatch	= 0;
	bool				add			= false;

	// Don't add this shape if it's not within the shapeMatches threshold
	if(weight < _weight)
		return 0;

	// If there's an upper limit on total matches, and it's been reached
	if(_total != 0 && _shapeMatches.size() == _total)
	{

		// Don't add this shape last stored is a better match than this one
		if(_shapeMatches.back()->weight() >= weight)
			return 0;

		// If new is better than stored worst, remove worst and store new
		delete _shapeMatches.back();
		_shapeMatches.pop_back();
		add = true;

	}
	else
	// No upper limit or limit not reached, stick this match on the list
		add = true;

	if(add == true)
		_shapeMatches.push_back
		(	shapeMatch = new ShapeMatch
			(	shape,
				weight,
				angle,
				scale,
				frame
			)
		);

	// Sort shapes in descending order, so best match is at start
	sort(_shapeMatches.begin(), _shapeMatches.end(), sortShapeMatches);

	return shapeMatch;

}

}
