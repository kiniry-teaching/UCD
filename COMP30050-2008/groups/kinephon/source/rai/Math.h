#ifndef __INTERPRETER_MATH_H__
#define __INTERPRETER_MATH_H__

#include <cmath>

namespace interpreter
{

class Math
{

public:
	/**
	 * Get some constant double PI
	 * @author EB
	 * @version 1.0
	 */
	static double const	PI(void);

public:
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
						(	float const	lineX1,
							float const	lineY1,
							float const	lineX2,
							float const	lineY2
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
						(	float const	pointX,
							float const	pointY,
							float const	circleX,
							float const	circleY,
							float const radius
						);
	/**
	 * Calculate if and where a line intersects a circle.
	 * If the line intersects in two points, only the outer impact point (based
	 *	on the diretion of the line (regardless of position line segment)) is
	 *	returned.
	 * http://www.vb-helper.com/howto_net_line_circle_intersections.html
	 * @param lineX x coordinate point on the line
	 * @param lineY y coordinate point on the line
	 * @param lineU x vector of line
	 * @param lineV y vector of line
	 * @param circleX the x coordinate of circle's centre
	 * @param circleY the y coordinate of circle's centre
	 * @param radius the radius of the circle
	 * @param impactX the x coordinate where the line impacts the circle. If
	 *	the line does not intersect the circle, this value is undefined
	 * @param impactY the y coordinate where the line impacts the circle. If
	 *	the line does not intersect the circle, this value is undefined
	 * @return true if the line intersected the circle
	 * @author EB
	 * @version 1.0
	 */
	static bool			calcLineIntersectCircle
						(	float const	lineX,
							float const	lineY,
							float const	lineU,
							float const	lineV,
							float const	circleX,
							float const	circleY,
							float const	radius,
							float &		impactX,
							float &		impactY
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
						(	float const	lineX1,
							float const	lineY1,
							float const	lineX2,
							float const	lineY2
						);
	/**
	 * Calculate if a value is inside a range of numbers in a small cyclic set
	 * @param value the value to be tested
	 * @param angle the value to test against
	 * @param range the range left or right of the angle
	 * @param total the total size of the cyclic set
	 * @return true if value is equal to angle +- range
	 * @author EB
	 * @version 1.0
	 */
	static bool			isValueInsideCyclicRange
						(	float const	value,
							float const	angle,
							float const	range,
							float const	total
						);

};

///////////////////////////////////////////////////////////////////////////////

inline double const Math::PI(void)
{	return 3.141592653589793238464;
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
	return (float)sqrt(dx * dx + dy * dy);
}

inline bool Math::isValueInsideCyclicRange
(	float const	value,
	float const	angle,
	float const	range,
	float const	total
){	float		dValue	= angle - value;

	if(dValue < 0)
		dValue = -dValue;

	if(dValue <= range || dValue >= total - range)
		return true;

	return false;

}

}

#endif
