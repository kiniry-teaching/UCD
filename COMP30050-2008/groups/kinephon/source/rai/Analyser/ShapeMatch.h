#ifndef __INTERPRETER_SHAPEMATCH_H__
#define __INTERPRETER_SHAPEMATCH_H__

#include "../../type.h"

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
	 * Be friends with ShapeMatches so it can create instance of this
	 * @author EB
	 * @version 1.0
	 */
	friend				class ShapeMatches;

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
	Shape const * const	shape						(void)	const;
	/**
	 * Return the weight the shape matched by
	 * @return The weight the shape matched by
	 * @author EB
	 * @version 1.0
	 */
	float				weight						(void)	const;
	/**
	 * Return the angle the shape had to be rotated to get this match
	 * @return The angle the shape had to be rotated to get this match
	 * @author EB
	 * @version 1.0
	 */
	float				angle						(void)	const;
	/**
	 * Return the value the shape had to be scaled by to get this match
	 * @return The value the shape had to be scaled by to get this match
	 * @author EB
	 * @version 1.0
	 */
	float				scale						(void)	const;
	/**
	 * Return the frame index where the match stopped
	 * @return The frame index where the match stopped
	 * @author EB
	 * @version 1.0
	 */
	uint				frame						(void)	const;
	/**
	 * Return a collection of any sub-shapes (speed/accel) that matched
	 * @return A collection of any sub-shapes (speed/accel) that matched. If
	 *	there are no sub-shapes, 0 is returned
	 * @author EB
	 * @version 1.0
	 */
	ShapeMatches * &	shapeMatches				(void);

///////////////////////////////////////////////////////////////////////////////
// friend *tor
//
private:
	/**
	 * Create a shape match.
	 * @param shape The shape that matched
	 * @param weight The weight by which the shape matched
	 * @param angle The angle by which the shape matched
	 * @param scale The scale by which the shape matched
	 * @param frame The last frame that was used in the match
	 * @author EB
	 * @version 1.0
	 */
						ShapeMatch
						(	Shape const * const		shape,
							float const				weight,
							float const				angle,
							float const				scale,
							uint const				frame
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
	Shape const * const	_shape;
	/**
	 * weight() field
	 * @author EB
	 * @version 1.0
	 * @see weight()
	 */
	float const			_weight;
	/**
	 * angle() field
	 * @author EB
	 * @version 1.0
	 * @see angle()
	 */
	float const			_angle;
	/**
	 * scale() field
	 * @author EB
	 * @version 1.0
	 * @see scale()
	 */
	float const			_scale;
	/**
	 * frame() field
	 * @author EB
	 * @version 1.0
	 * @see frame()
	 */
	uint const			_frame;
	/**
	 * shapeMatches() field
	 * @author EB
	 * @version 1.0
	 * @see shapeMatches()
	 */
	ShapeMatches *		_shapeMatches;

};

///////////////////////////////////////////////////////////////////////////////

inline ShapeMatch::ShapeMatch
(	Shape const * const	shape,
	float const			weight,
	float const			angle,
	float const			scale,
	uint const			frame
) :	_shape				(shape),
	_weight				(weight),
	_angle				(angle),
	_scale				(scale),
	_frame				(frame),
	_shapeMatches		(0)
{ }

inline Shape const * const ShapeMatch::shape(void) const
{	return _shape;
}

inline float ShapeMatch::weight(void) const
{	return _weight;
}

inline ShapeMatches * & ShapeMatch::shapeMatches(void)
{	return _shapeMatches;
}

}

#endif
