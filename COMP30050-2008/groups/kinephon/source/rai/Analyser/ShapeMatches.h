#ifndef __INTERPRETER_SHAPEMATCHES_H__
#define __INTERPRETER_SHAPEMATCHES_H__

#include <vector>
#include "ShapeMatch.h"
using std::vector;

namespace interpreter
{

/**
 * A collection of matching shapes.
 * This collection may contain movement, speed, or accel shapes, but their type
 *	will not be specified. It is up to the shape designer to correctly name the
 *	shape so they can be identified
 * @author EB
 * @version 1.0
 */
class ShapeMatches
{

public:
	/**
	 * Create a shape match collection.
	 * @param weight The weight a shape must match against to be included in
	 *	the collection. All shapes whose weight are greater or equal are added.
	 * @param total The total number of shapes to match. Only the highest
	 *	matching shapes are include if the number of matches goes over this
	 *	total. Defaults to 1 meaning match only the highest matching shape
	 *	that's not less than weight. If total == 0, all shapes within the
	 *	weight range are included
	 * @author EB
	 * @version 1.0
	 */
							ShapeMatches
							(	float const * const			weight,
								uint const					total	= 1
							);

public:
	/**
	 * Return the total number of shapes matched
	 * @return The total number of shapes matched
	 * @author EB
	 * @version 1.0
	 */
	uint					length							(void)	const;

	/**
	 * Return the indexed matched shape. 
	 * @param index The index of the matched shape. Shapes will be indexed from
	 *	strong to weakly matched. Index should be in the range (0..length()-1)
	 * @return A structure containing the indexed matched shape along with the
	 *	weight of the match and any sub shapes matched (speed/accel)
	 * @author EB
	 * @version 1.0
	 * @pre index >= 0 && index < length();
	 * @post /value != 0;
	 */
	ShapeMatch *			operator[]
							(	uint const					index
							)	const;

	/**
	 * Add a shape match to the collection.
	 * This may change the order of the indexed shapes so calling this[0]
	 *	before and after calling this may return different values as the
	 *	matched shapes will be sorted and possibly trimmed to meet the
	 *	maximum total set in the constructor
	 * @param shapeMatch The new matched shape to add
	 * @return Reference to this
	 * @author EB
	 * @version 1.0
	 */
	ShapeMatches &			operator+=
							(	ShapeMatch const * const	shapeMatch
							);

private:
	/**
	 * Sorted array of matching shapes
	 * @author EB
	 * @version 1.0
	 */
	vector<ShapeMatch> *	_shapeMatches;

};

}

#endif
