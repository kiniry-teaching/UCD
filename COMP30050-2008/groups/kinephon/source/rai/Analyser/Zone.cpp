#include "../Math.h"
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
inline bool Zone::isInside
(	float const	x,
	float const	y,
	float const	u,
	float const	v,
	float const	radius,
	float const	angle,
	float const	arc
)	const
{	float		ix;
	float		iy;
	float		iAngle;

	// Calculate where the line impacts the circle
	if(Math::calcLineIntersectCircle
	(	x, y,
		u, v,
		_x, _y,
		radius,
		ix, iy
	) == true)
	{

		// Calculate the angle between the circle centre and the impact point
		iAngle = Math::calcSegmentAngle(_x, _y, ix, iy);

		if(Math::isValueInsideCyclicRange
		(	iAngle,
			angle,
			arc,
			(float)(Math::PI() * 2)
		) == false)
			return false;

	}
	else
		return false;

	return true;

}

///////////////////////////////////////////////////////////////////////////////
// test
//
ezt Zone::test
(	float const	x,
	float const	y,
	float const	u,
	float const	v,
	bool const	isEntered
)	const
{	bool		isStartInside;
	bool		isEndInside;
	int			result;

	// If we're not suppose to be inside this zone..
	if(isEntered == false)
	{

		isStartInside	= isInside(x, y, _enterRadius);
		isEndInside		= isInside(x + u, y + v, _enterRadius);

		// ..and we're not inside this zone
		if(isStartInside == false)
			// ..and we've just gone inside this zone
			if(isEndInside == true)
				// ..and we've entered through the correct angle/arc,
				//	we've entered
				if(isInside
				(	x, y,
					u, v,
					_enterRadius,
					_enterAngle,
					_enterArc
				) == true)
					result = ezone::ENTERED;
				else
				// ..or we've not entered correctly, we've not entered
					result = ezone::NOCHANGE;
			else
			// ..or we're still not inside this zone, ignore
				result = ezone::NOCHANGE;
		else
		// ..or we're inside this zone, there's a problem
			result = ezone::FAILED;

	}
	else
	// ..or we are suppose to be inside this zone..
	{

		isStartInside	= isInside(x, y, _exitRadius);
		isEndInside		= isInside(x + u, y + v, _exitRadius);

		// ..and we are inside this zone
		if(isStartInside == true)
			// ..and we've just gone outside this zone
			if(isEndInside == false)
				// ..and we've exited through the correct angle/arc,
				//	we've exited
				if(isInside
				(	x, y,
					u, v,
					_exitRadius,
					_exitAngle,
					_exitArc
				) == false)
					result = ezone::EXITED;
				else
				// ..or we've not exited correctly, there's a problem
					result = ezone::FAILED;
			else
			// ..or we've still inside this zone, ignore
				result = ezone::NOCHANGE;
		else
		// ..or we are outside this zone, there's a problem
			result = ezone::FAILED;

	}

	return result;

}

}
