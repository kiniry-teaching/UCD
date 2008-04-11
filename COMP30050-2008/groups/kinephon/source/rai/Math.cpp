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
		angle = (float)(dy == 0 ? 0 : dy < 0 ? (PI() + PI() / 2) : (PI() / 2));

	return (float)angle;

}

///////////////////////////////////////////////////////////////////////////////
// line intersect circle
//
bool Math::calcLineIntersectCircle
(	float const	lineX,
	float const	lineY,
	float const	lineU,
	float const	lineV,
	float const	circleX,
	float const	circleY,
	float const	radius,
	float &		impactX,
	float &		impactY
){	float const	lx		= lineX - circleX;
	float const	ly		= lineY - circleY;
	float const	a		= lineU * lineU + lineV * lineV;
	float const	b		= 2 * (lineU * lx + lineV * ly);
	float const	c		= lx * lx + ly * ly - radius * radius;
	float const	det		= b * b - 4 * a * c;
	float		t;
	float		t2;
	float		t3;

	// Not intersect
	if(a <= Math::ZERO() || det < 0.0f)
		return false;
	else
	// Tangent - almost 
	if(Math::isZero(det) == true)
		t = -b / (2 * a);
	else
	// Intersect 2 points
	{	// Precalculate
		t2 = -b / 2 * a;
		t3 = (float)(sqrt(det) / 2 * a);
		// Hit direction, pick line direction impact outside circle
		if(t2 + t3 > t2 - t3)
			t = t2 + t3;
		else
			t = t2 - t3;
	}

	impactX = lineX + t * lineU;
	impactX = lineX + t * lineV;

	return true;

}

}
