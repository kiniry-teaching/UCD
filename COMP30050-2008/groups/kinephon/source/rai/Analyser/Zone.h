#ifndef __INTERPRETER_ZONE_H__
#define __INTERPRETER_ZONE_H__

#include "../../type.h"

namespace interpreter
{

/**
 * List of possible results from Zone::test()
 * @author EB
 * @version 1.0
 */
namespace ezone
{
	/**
	 * The zone was neither entered nor exited. This means it's either still
	 *	outside the zone, or still inside the zone
	 */
	ezt const	NOCHANGE	= 0;
	/**
	 * The zone was entered correctly
	 * @author EB
	 * @version 1.0
	 */
	ezt const	ENTERED		= 1;
	/**
	 * The zone was exited correctly
	 * @author EB
	 * @version 1.0
	 */
	ezt const	EXITED		= 2;
	/**
	 * The zone was exited incorrectly. The zone should be considered as not
	 *	entered in this case
	 * @author EB
	 * @version 1.0
	 */
	ezt const	FAILED		= 3;
}

/**
 * A list of zones within a shape that must be passed for the shape to match.
 *	This is used to prevent shapes that have complete partial matches or going
 *	in the wrong direction being matched. This class is private to all parts
 *	of the project except ShapeLoader and Shape
 */
class Zone
{

///////////////////////////////////////////////////////////////////////////////
// friends
//
	/**
	 * Be friends with ShapeLoader so it can load the zones
	 * @author EB
	 * @version 1.0
	 */
	friend	class ShapesLoader;
	/**
	 * Be friends with Shape so it can test the zones
	 * @author EB
	 * @version 1.0
	 */
	friend	class Shape;

#if __TEST__
///////////////////////////////////////////////////////////////////////////////
// tests
//
public:
	/**
	 * Execute a number of test cases for this class
	 * @author EB
	 * @version 1.0
	 */
	static void	RunTest(void);
#endif

///////////////////////////////////////////////////////////////////////////////
// private commands
//
private:
	/**
	 * Determine whether a point is inside a given radius
	 * @param x The x co-ordinate of the point to test
	 * @param y The y co-ordinate of the point to test
	 * @param radius The radius to test, will be either enterRadius or
	 *	exitRadius
	 */
	bool	isInside
			(	float const	x,
				float const	y,
				float const	radius
			)	const;
	/**
	 * Determine if the entry point (point at which a line segment intersects
	 *	a given radius) is within the zone's radius, angle and arc
	 * @param x The x co-ordinate of the segment start to test
	 * @param y The y co-ordinate of the segment start to test
	 * @param u The x co-ordinate of the segment's vector to test
	 * @param v The y co-ordinate of the segment's vector to test
	 * @param radius The radius to test, will be either enterRadius or
	 *	exitRadius
	 * @param angle The angle to test, will be either enterAngle or exitAngle
	 * @param arc The arc to test, will be either enterArc or exitArc
	 */
	bool	isInside
			(	float const	x,
				float const	y,
				float const	u,
				float const	v,
				float const	radius,
				float const	angle,
				float const	arc
			)	const;

///////////////////////////////////////////////////////////////////////////////
// friend (ShapeLoader) *tor
//
private:
	/**
	 * Create a new zone. This will only be called by ShapeLoader. All
	 *	angles are in radians
	 * @param x The x co-ordinate of the zone
	 * @param y The y co-ordinate of the zone
	 * @param enterRadius The radius a point must be from the zone to be
	 *	considered as having entered the zone
	 * @param exitRadius The radius a point must be from the zone to be
	 *	considered as having exited the zone. With this larger than the
	 *	enterRadius, an accidental jitter exit will be avoided
	 * @param enterAngle The angle from which a point must enter to be
	 *	considered as having entered the zone
	 * @param exitAngle The angle from which a point must exit to be
	 *	considered as having exited the zone. Exiting from a different
	 *	angle will result in the zone being considered as not entered
	 * @param enterArc The arc clockwise and counter-clockwise off the
	 *	enter angle that will also be allowable angles to enter from.
	 *	An angle greater than 2pi will mean any angle can be entered
	 * @param exitArc The arc clockwise and counter-clockwise off the
	 *	exit angle that will also be allowable angles to exit from
	 *	An angle greater than 2pi will mean any angle can be exited
	 * @author EB
	 * @version 1.0
	 */
			Zone
			(	float const	x,
				float const	y,
				float const	enterRadius,
				float const	exitRadius,
				float const	enterAngle,
				float const	exitAngle,
				float const	enterArc,
				float const	exitArc
			);

///////////////////////////////////////////////////////////////////////////////
// friend (Shape) commands
//
private:
	/**
	 * Tests a movement segment to see how the move interacted with this zone
	 * @param x The x co-ordinate of the movement to test
	 * @param y The y co-ordinate of the movement to test
	 * @param u The x vector the movement is making
	 * @param v The y vector the movement is making
	 * @param isEntered True if this zone has been entered (a previous test
	 *	returned ezone::ENTERED), false otherwise
	 * @return Returns how the move interacted with the zone. Values are
	 *	enumerated in ezone
	 * @see ezone
	 * @author EB
	 * @version 1.0
	 */
	ezt		test
			(	float const	x,
				float const	y,
				float const	u,
				float const	v,
				bool const	isEntered
			)	const;

///////////////////////////////////////////////////////////////////////////////
// fields
//
private:
	/**
	 * Store the x co-ordinate of this zone
	 * @author EB
	 * @version 1.0
	 */
	float	_x;
	/**
	 * Store the y co-ordinate of this zone
	 * @author EB
	 * @version 1.0
	 */
	float	_y;
	/**
	 * Store the radius of the zone's entry
	 * @author EB
	 * @version 1.0
	 */
	float	_enterRadius;
	/**
	 * Store the radius of the zone's exit
	 * @author EB
	 * @version 1.0
	 */
	float	_exitRadius;
	/**
	 * Store the angle of the zone's entry
	 * @author EB
	 * @version 1.0
	 */
	float	_enterAngle;
	/**
	 * Store the angle of the zone's exit
	 * @author EB
	 * @version 1.0
	 */
	float	_exitAngle;
	/**
	 * Store the arc off the angle of the zone's entry
	 * @author EB
	 * @version 1.0
	 */
	float	_enterArc;
	/**
	 * Store the arc off the angle of the zone's exit
	 * @author EB
	 * @version 1.0
	 */
	float	_exitArc;

};

///////////////////////////////////////////////////////////////////////////////

inline Zone::Zone
(	float const		x,
	float const		y,
	float const		enterRadius,
	float const		exitRadius,
	float const		enterAngle,
	float const		exitAngle,
	float const		enterArc,
	float const		exitArc
) :	_x				(x),
	_y				(y),
	_enterRadius	(enterRadius),
	_exitRadius		(exitRadius),
	_enterAngle		(enterAngle),
	_exitAngle		(exitAngle),
	_enterArc		(enterArc),
	_exitArc		(exitArc)
{ }

}

#endif
