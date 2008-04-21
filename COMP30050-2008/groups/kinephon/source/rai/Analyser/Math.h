#ifndef __INTERPRETER_MATH_H__
#define __INTERPRETER_MATH_H__

#include <cmath>
#include "../../type.h"
#include "Point.h"

namespace interpreter
{

/**
 * Collection of useful (to me) math funtions
 */
class Math
{

public:
	/**
	 * A constant supply of double delicious PI
	 * @author EB
	 * @version 1.0
	 */
	static double const	PI					(void);
	/**
	 * Get a value near zero
	 * @author EB
	 * @version 1.0
	 */
	static float const	ZERO				(void);

public:
	/**
	 * Calculate if a float value is approx. zero
	 * @param value The value to test
	 * @return true if value is approx. zero
	 * @author EB
	 * @version 1.0
	 */
	static bool			isZero
						(	float const		value
						);
	/**
	 * Calculate the angle of a line that passes between two points in radians
	 * @param lineX1 first point, x coordinate, that line passes
	 * @param lineY1 first point, y coordinate, that line passes
	 * @param lineX2 second point, x coordinate, that line passes
	 * @param lineY2 second point, y coordinate, that line passes
	 * @return the angle of the line in radians
	 * @author EB
	 * @version 1.0
	 */
	static float		calcSegmentAngle
						(	float const		lineX1,
							float const		lineY1,
							float const		lineX2,
							float const		lineY2
						);
	/**
	 * Calculate if a point lies inside a circle
	 * @param pointX the x coordinate of the point to test
	 * @param pointY the y coordinate of the point to test
	 * @param circleX the x coordinate of circle's centre
	 * @param circleY the y coordinate of circle's centre
	 * @param radius the radius of the circle
	 * @return true if the point is inside the circle
	 * @author EB
	 * @version 1.0
	 */
	static bool			isPointInsideCircle
						(	float const		pointX,
							float const		pointY,
							float const		circleX,
							float const		circleY,
							float const		radius
						);
	/**
	 * Calculate if and where a line intersects a circle.
	 * The segment must intersect the circle to return true. If true
	 *	is not returned, the value of impactX and impactY is undefined
	 * http://www.vb-helper.com/howto_net_line_circle_intersections.html
	 * @param lineX1 first point, x coordinate, that line passes
	 * @param lineY1 first point, y coordinate, that line passes
	 * @param lineX2 second point, x coordinate, that line passes
	 * @param lineY2 second point, y coordinate, that line passes
	 * @param circleX the x coordinate of circle's centre
	 * @param circleY the y coordinate of circle's centre
	 * @param radius the radius of the circle
	 * @param impactX [out] the x coordinate where the line impacts the circle. If
	 *	the line does not intersect the circle, this value is undefined
	 * @param impactY [out] the y coordinate where the line impacts the circle. If
	 *	the line does not intersect the circle, this value is undefined
	 * @param impactOutside if true, the impact point will be the one on the
	 *	outside of the circle, otherwise it will be the impact on the inside
	 * @return true if the line intersected the circle
	 * @note http://www.vb-helper.com/howto_net_line_circle_intersections.html
	 * @author EB
	 * @version 1.0
	 */
	static bool			calcSegmentIntersectCircle
						(	float const		lineX1,
							float const		lineY1,
							float const		lineX2,
							float const		lineY2,
							float const		circleX,
							float const		circleY,
							float const		radius,
							float &			impactX,
							float &			impactY,
							bool			impactOutside
						);
	/**
	 * Calculate the length of a line that passes between two points
	 * @param lineX1 first point, x coordinate, that line passes
	 * @param lineY1 first point, y coordinate, that line passes
	 * @param lineX2 second point, x coordinate, that line passes
	 * @param lineY2 second point, y coordinate, that line passes
	 * @return the length of the line
	 * @author EB
	 * @version 1.0
	 */
	static float		calcSegmentLength
						(	float const		lineX1,
							float const		lineY1,
							float const		lineX2,
							float const		lineY2
						);
	/**
	 * Calculate if a value is inside a range of numbers in a small cyclic set
	 * @param value1 the value to be tested
	 * @param value2 the value to test against
	 * @param range the range left or right of the angle
	 * @param set the total size of the cyclic set
	 * @return true if value is equal to angle +- range
	 * @author EB
	 * @version 1.0
	 */
	static bool			isValueDeltaInsideCyclicSetRange
						(	float const		value1,
							float const		value2,
							float const		range,
							float const		set
						);
	/**
	 * Calculate the difference between two values in a cyclic set
	 * @param value1 the value to be tested
	 * @param value2 the value to test against
	 * @param set the total size of the cyclic set
	 * @return difference between values so that
	 *	(value1 + /result) % set == value2;
	 * @author EB
	 * @version 1.0
	 */
	static float		calcValueDeltaInsideCyclicSet
						(	float const		value1,
							float const		value2,
							float const		set
						);

};

///////////////////////////////////////////////////////////////////////////////

inline double const Math::PI(void)
{	return 3.141592653589793238464;
}

inline float const Math::ZERO(void)
{	return 1.0e-4f;
}

inline bool Math::isZero
(	float const value
){	return value >= -Math::ZERO() && value <= Math::ZERO();
}

inline bool Math::isPointInsideCircle
(	float const	pointX,
	float const	pointY,
	float const	circleX,
	float const	circleY,
	float const radius
){	float const	dx = pointX - circleX;
	float const	dy = pointY - circleY;
	return dx * dx + dy * dy <= radius * radius;
}

inline float Math::calcSegmentLength
(	float const	lineX1,
	float const	lineY1,
	float const	lineX2,
	float const	lineY2
){	float const	dx = lineX2 - lineX1;
	float const	dy = lineY2 - lineY1;
	return static_cast<float>(sqrt(dx * dx + dy * dy));
}

inline bool Math::isValueDeltaInsideCyclicSetRange
(	float const	value1,
	float const	value2,
	float const	range,
	float const	total
){	float		delta	= value2 - value1;

	if(delta < 0)
		delta = -delta;

	if(delta <= range || delta >= total - range)
		return true;

	return false;

}

inline float Math::calcValueDeltaInsideCyclicSet
(	float const	value1,
	float const	value2,
	float const	set
){	float		delta	= value2 - value1;

	if(delta < 0)
		delta = -delta;

	if(delta >= set / 2)
		delta -= set;

	if(value1 > value2)
		return -delta;

	return delta;

}

}

#endif
