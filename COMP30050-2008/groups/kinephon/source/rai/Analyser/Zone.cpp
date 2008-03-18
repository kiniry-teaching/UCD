#include "zone.h"

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
{	float const	dx = x - _x;
	float const	dy = y - _y;
	return dx * dx + dy * dy <= radius * radius;
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
{

	// @todo isInside. Get intersect on radius and angle to intersect

	return false;

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
