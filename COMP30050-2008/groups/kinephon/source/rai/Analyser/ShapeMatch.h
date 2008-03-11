#ifndef __INTERPRETER_SHAPEMATCH_H__
#define __INTERPRETER_SHAPEMATCH_H__

namespace interpreter
{

class Shape;
class ShapeMatches;

/**
 * A structure containing a matched shape and the weight of the match as well
 *	as a collection of sub matched shapes (speed or accel) if any
 * @author EB
 * @version 1.0
 */
class ShapeMatch
{

///////////////////////////////////////////////////////////////////////////////
// friends
//
	/**
	 * Be friends with Shape so it can create matches
	 * @author EB
	 * @version 1.0
	 */
	friend	class Shape;

///////////////////////////////////////////////////////////////////////////////
// queries
//
public:
	/**
	 * Return the shape that matched
	 * @return The shape that matched
	 * @author EB
	 * @version 1.0
	 */
	Shape *			shape						(void)	const;
	/**
	 * Return the weight the shape matched by
	 * @return The weight the shape matched by
	 * @author EB
	 * @version 1.0
	 */
	float			weight						(void)	const;
	/**
	 * Return a collection of any sub-shapes (speed/accel) that matched
	 * @return A collection of any sub-shapes (speed/accel) that matched. If
	 *	there are no sub-shapes, 0 is returned
	 * @author EB
	 * @version 1.0
	 */
	ShapeMatches *	shapeMatches				(void);
	
///////////////////////////////////////////////////////////////////////////////
// friend *tor
//
private:
	/**
	 * Create a shape match.
	 * @param shape The shape that made the match
	 * @param weight The weight the shape matched by
	 * @author EB
	 * @version 1.0
	 */
					ShapeMatch
					(	Shape * const			shape,
						float const				weight
					);

///////////////////////////////////////////////////////////////////////////////
// fields
//
private:
	/**
	 * shape() field
	 * @author EB
	 * @version 1.0
	 * @see shape()
	 */
	Shape *			_shape;
	/**
	 * weight() field
	 * @author EB
	 * @version 1.0
	 * @see weight()
	 */
	float			_weight;
	/**
	 * shapeMatches() field
	 * @author EB
	 * @version 1.0
	 * @see shapeMatches()
	 */
	ShapeMatches *	_shapeMatches;

};

///////////////////////////////////////////////////////////////////////////////

inline ShapeMatch::ShapeMatch
(	Shape * const			shape,
	float const				weight
) :	_shape					(shape),
	_weight					(weight)
{ }

inline ShapeMatches * ShapeMatch::shapeMatches(void)
{//	if(_shapeMatches == 0)
//		return _shapeMatches = new ShapeMatches;
	return _shapeMatches;
}

}

#endif
