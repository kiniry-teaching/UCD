#include "Math.h"
#include "Zone.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// is inside radius
//
inline bool Zone::isInside
(	float const	x,
	float const	y,
	float const	radius
)	const
{	return Math::isPointInsideCircle(x, y, _x, _y, radius);
}

///////////////////////////////////////////////////////////////////////////////
// is inside angle arc
//
inline bool Zone::testAngle
(	float const	x,
	float const	y,
	float const	angle,
	float const	arc
)	const
{	float		impactAngle;

	// Calculate the angle between the circle centre and the impact point
	impactAngle = Math::calcSegmentAngle(_x, _y, x, y);

	return Math::isValueDeltaInsideCyclicSetRange
	(	impactAngle,
		angle,
		arc,
		static_cast<float>(Math::PI() + Math::PI())
	);

}

///////////////////////////////////////////////////////////////////////////////
// test
//
void Zone::compare
(	float const	x1,
	float const	y1,
	float const	x2,
	float const	y2,
	ezr &		result,
	ezm const	mode			//= ezmode::NORMAL
)	const
{	float		enterImpactX;
	float		enterImpactY;
	float		exitImpactX;
	float		exitImpactY;

	// Test if this move entered the zone
	if(Math::calcSegmentIntersectCircle
	(	x1, y1,
		x2, y2,
		_x, _y,
		_enterRadius,
		enterImpactX, enterImpactY,
		true	// Enter impact point
	) == true
	// If it didn't enter during init, is the start point already inside?
	|| mode == ezmode::INITIALIZE
	&& isInside(x1, y1, _enterRadius) == true)
		// If normal mode, must test that the impact point was on angle
		if(mode == ezmode::NORMAL)
			if(testAngle
			(	enterImpactX,
				enterImpactY,
				_enterAngle,
				_enterArc
			) == true)
				result = ezresult::ENTERED;
			else
				// If it didn't enter the correct angle, it just didn't enter
				//	so it's a no change, rather than an erro
				result = ezresult::NOCHANGE;
		// If initalise mode, it's entered
		else
			result = ezresult::ENTERED;
	else
		result = ezresult::NOCHANGE;

	// Test if this move exited the zone. But only do the test if the zone has
	//	been entered before
	if((result & ezresult::ENTERED) == ezresult::ENTERED)
		if(Math::calcSegmentIntersectCircle
		(	x1, y1,
			x2, y2,
			_x, _y,
			_exitRadius,
			exitImpactX, exitImpactY,
			false	// Exit impact point
		) == true)
			// Must always exit correctly regardless of mode
			if(testAngle
			(	exitImpactX,
				exitImpactX,
				_exitAngle,
				_exitArc
			) == true)
				// If it exited, include the exited information
				result = ezresult::PASSED;
			else
				// If it exited at a bad angle, it's an error, 
				result = ezresult::FAILED;

}

}
