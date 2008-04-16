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
void ShapeMatches::operator +=
(	ShapeMatch * const	shapeMatch
){

	// Don't add this shape if it's not within the shapeMatches threshold
	if(shapeMatch->weight() < _weight)
		return;

	// If there's an upper limit on total matches, and it's been reached
	if(_total != 0 && _shapeMatches.size() == _total)
	{

		// Don't add this shape last stored is a better match than this one
		if(_shapeMatches.back()->weight() >= shapeMatch->weight())
			return;

		// If new is better than stored worst, remove worst and store new
		_shapeMatches.pop_back();
		_shapeMatches.push_back(shapeMatch);

	}
	else
	// No upper limit or limit not reached, stick this match on the list
		_shapeMatches.push_back(shapeMatch);

	// Sort shapes in descending order, so best match is at start
	sort(_shapeMatches.begin(), _shapeMatches.end(), sortShapeMatches);

}

}
