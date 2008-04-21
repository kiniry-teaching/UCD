#include "Math.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// line angle
//
float Math::calcSegmentAngle
(	float const	lineX1,
	float const	lineY1,
	float const	lineX2,
	float const	lineY2
){	double		angle;
	float const	dx		= lineX2 - lineX1;
	float const	dy		= lineY2 - lineY1;

	if(dx != 0)
	{

		// Get angle
		angle = atan(dy / dx);

		// Fix angle
		if (dx < 0) angle += PI();
		if (dx >= 0 && dy < 0) angle += PI() + PI();

	}
	else
		angle = (dy == 0 ? 0 : dy < 0 ? (PI() + PI() / 2) : (PI() / 2));

	return static_cast<float>(angle);

}

///////////////////////////////////////////////////////////////////////////////
// line intersect circle
//
bool Math::calcSegmentIntersectCircle
(	float const	lineX1,
	float const	lineY1,
	float const	lineX2,
	float const	lineY2,
	float const	circleX,
	float const	circleY,
	float const	radius,
	float &		impactX,
	float &		impactY,
	bool		impactOutside
){	float const	lineU			= lineX2 - lineX1;
	float const	lineV			= lineY2 - lineY1;
	float const	circleU			= lineX1 - circleX;
	float const	circleV			= lineY1 - circleY;
	float const	a				= lineU * lineU + lineV * lineV;
	float const	b				= 2 * (lineU * circleU + lineV * circleV);
	float const	c				= circleU * circleU
								+ circleV * circleV
								- radius * radius;
	float const	d				= b * b - 4 * a * c;
	float		t;
	float		t2;
	float		t3;

	// Not intersect
	if(a <= Math::ZERO() || d < 0.0f)
		return false;
	else
	// Tangent - almost 
	if(Math::isZero(d) == true)
		t = -b / (2 * a);
	else
	// Intersect 2 points
	{	// Precalculate
		t2 = -b / (2 * a);
		t3 = static_cast<float>(sqrt(d) / (2 * a));
		// Pick the impact on the side of the circle the line travels
		//	and also whether the impact should be inside or outside
		if((t3 < 0) ^ impactOutside)
			t = t2 - t3;
		else
			t = t2 + t3;
	}

	// Line didn't touch the circle, no impact
	if(t < 0.0f || t > 1.0f)
		return false;

	impactX = lineX1 + t * lineU;
	impactY = lineY1 + t * lineV;

	return true;

}

}
