#include "Math.h"
#include "Points.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// smooth
//
void Points::smoothen
(	uchar const	range,
	epr const	affect
){	short *		tempPoints;
	uint		index;
	int			result		= 0;

	// There will be no smoothing, just exit
	if(range == 0)
		return;

	// Create temporary buffer to store smooth points. tempPoints is only a
	//	short as it will only ever work with one axis at a time
	tempPoints = new short[_length];

	// Calculate the initial smoothing window left and right of the first point
	//  Because there are no points left of the first point, the first point
	//	is used instead (same with the last point and no right points (below))
	for
	(	index = 0;
		index < range && index < _length;
		index++
	)	result += _points[0].raw[affect] + _points[index].raw[affect];

	for(index = 0; index < _length; index++)
	{

		// Shift the smoothing opening window across the points
		if(index + range < _length)
			result += _points[index + range].raw[affect];
		else
			result += _points[_length - 1].raw[affect];

		// Calculate and store smooth result
		tempPoints[index] = static_cast<short>(result / ((range << 1) + 1));

		// Shift the smoothing closing window across the points
		if(index >= range)
			result -= _points[index - range].raw[affect];
		else
			result -= _points[0].raw[affect];

	}

	// Copy the updated points over the original
	for(index = 0; index < _length; index++)
		_points[index].raw[affect] = tempPoints[index];

	// Deallocate temporary storage
	delete [] tempPoints;

}

///////////////////////////////////////////////////////////////////////////////
// sharp
//
void Points::sharpen
(	float const	angle,
	esp const	prune
){	uint		length;
	uint		index;
	float		angle1;
	float		angle2;

	// Need at least 3 points (x, y) to do a sharpen
	if(_length < 3)
		return;

	// Start sharpening

	// Calculate the angle from the first point to the second which is the
	//	base angle off which the following angle will be tested
	angle1 = Math::calcSegmentAngle
	(	_points[0].x, _points[0].y,
		_points[1].x, _points[1].y
	);

	// Go through all points except the first and last
	for(index = length = 1; index < _length - 1; index++)
	{

		// Calculate the angle to next point
		angle2 = Math::calcSegmentAngle
		(	_points[index    ].x, _points[index    ].y,
			_points[index + 1].x, _points[index + 1].y
		);

		// If the angle is outside the angle range, it is carried on to the
		//	output and the resulting vector's angle becomes the new base
		if(Math::isValueDeltaInsideCyclicSetRange
		(	angle1,
			angle2,
			angle,
			static_cast<float>(Math::PI() + Math::PI())
		) == prune)
		{

			// Store this new point overwriting an old (removed) point in the
			//	current array - but only if the overwriting point is not the
			//	point being tested as it'll be overwriting itself
			if(index != length)
			{	_points[length].frame = _points[index].frame;
				_points[length].x = _points[index].x;
				_points[length].y = _points[index].y;
			}

			// Set new base angle to the angle of the newly created vector
			angle1 = Math::calcSegmentAngle
			(	_points[length - 1].x,
				_points[length - 1].y,
				_points[length    ].x,
				_points[length    ].y
			);
			length++;

		}
		else
		// else, ignore this point and continue looking for an angle that's
		//	too far off the base angle, unless pruning outside the angle,
		//	in which case, recalculate the base where it didn't prune
		if(prune == eprune::OUTER)
			angle1 = Math::calcSegmentAngle
			(	_points[index - 1].x, _points[index - 1].y,
				_points[index    ].x, _points[index    ].y
			);

	}

	// Make sure the last point is part of the final output
	if(_length > 1 && _length != length)
	{	_points[length].frame = _points[_length - 1].frame;
		_points[length].x = _points[_length - 1].x;
		_points[length].y = _points[_length - 1].y;
		length++;
	}

	_length = length;

}

}
