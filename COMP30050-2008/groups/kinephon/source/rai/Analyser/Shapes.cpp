#include "shapes.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// compare
//
bool Shapes::compare
(	Track const * const		track,
	ShapeMatches * const	shapeMatches
)	const
{	uint					index;
	bool					anyCompare		= false;

	// Compare against each shape and set anyCompare to true if
	//	one or more matches are made
	for(index = 0; index < _shapeIndex; index++)
		anyCompare = (*_shapes)[index].compare
		(	track,
			shapeMatches
		)
		| anyCompare;

	return anyCompare;

}

///////////////////////////////////////////////////////////////////////////////
// add
//
void Shapes::operator +=
(	Shape *	shape
){

	// Only add the shape if there's space to do so
	if(_shapeIndex < _nShapes)
		*(_shapes + _shapeIndex) = shape;

}

///////////////////////////////////////////////////////////////////////////////
// ctor
//
Shapes::Shapes
(	uint		length
) :	_nShapes	(length),
	_shapeIndex	(0)
{	_shapes = new Shape * [length];
}

///////////////////////////////////////////////////////////////////////////////
// dtor
//
Shapes::~Shapes(void)
{	uint	index;

	// Though the ShapeLoader created the shape object,
	//	because it is internal in the Analyser, don't
	//	bother get the ShapeLoader to destroy it, both
	//	are guaranteed to operate on the same heap
	for(index = 0; index < _shapeIndex; index++)
		delete *(_shapes + index);
	delete (*_shapes);

}


}
