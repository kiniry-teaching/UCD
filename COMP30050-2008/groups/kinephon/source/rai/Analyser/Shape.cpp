#include "Math.h"
#include "ShapeMatch.h"
#include "Shape.h"

namespace interpreter
{

/*extern*/ SHAPE_EDIT_HOOK shapeEditHook = 0;

///////////////////////////////////////////////////////////////////////////////
// compare
//
ShapeMatch * Shape::compare
(	Points &				origPoints,
	ShapeMatches * const	shapeMatches
)	const
{	Points					points;
	float					zoneAngle;
	float					zoneScale;
	uint					index;
	float					weight		= -1.0f;
	float					angle;
	float					scale;
	float					bestWeight	= -1.0f;
	float					bestAngle	= 0.0f;
	float					bestScale	= 1.0f;
	uint					bestFrame	= 1;
	ShapeMatch *			shapeMatch	= 0;
/*
	if(origPoints.length() >= 3)
	{	origPoints[0].x = 24;
		origPoints[0].y = 9;
		origPoints[1].x = 22;
		origPoints[1].y = 26;
		origPoints[2].x = 4;
		origPoints[2].y = 9;
		origPoints.length() = 3;
	}
*/
	// Precalculate the zone's angle and scale, it is used in every test
	zoneAngle = Math::calcSegmentAngle
	(	_zones[_nZones - 1]->_x, _zones[_nZones - 1]->_y,
		_zones[_nZones - 2]->_x, _zones[_nZones - 2]->_y
	);

	zoneScale = Math::calcSegmentLength
	(	_zones[_nZones - 1]->_x, _zones[_nZones - 1]->_y,
		_zones[_nZones - 2]->_x, _zones[_nZones - 2]->_y
	);

	if(zoneScale < 1.0f)
		return 0;

	// Try every possibility to find a match! Even if a match is found,
	//	continue looking for better and better matches
	for(index = 1; index < origPoints.length(); index++)
		// Rotate, scale, and crop
		if(prepare
		(	origPoints, points,
			index,
			angle, scale,
			zoneAngle, zoneScale
		) == true
		// Compare against zone data
		&& follow(points) == true)
			// Compare against weight data
			if((weight = weigh(points)) > bestWeight)
			{

				bestWeight = weight;
				bestAngle = angle;
				bestScale = scale;
				bestFrame = points.length();

				shapeEditHook(0, points);

				// Can't get much better - well, actually could
				//	if a better angle or scale was found, but whatever
				if(Math::isZero(weight - 1.0f) == true)
					break;

			}

	// Add this shape if the best match was best enough
	shapeMatch = shapeMatches->add
	(	this,
		bestWeight,
		bestAngle,
		bestScale,
		bestFrame
	);

	return shapeMatch;

}

///////////////////////////////////////////////////////////////////////////////
// prepare
//
bool Shape::prepare
(	Points &	origPoints,
	Points &	points,
	uint		index,
	float &		angle,
	float &		scale,
	float		zoneAngle,
	float		zoneScale
)	const
{	short		tformX;
	short		tformY;
	short		x;
	short		y;
	short		lastX;
	short		lastY;
	float		cosTheta;
	float		sinTheta;
	uint		last		= origPoints.length() - 1;

	// Note: point data runs 0..length as old to new. Prepare matches new data
	//	first, runs new to old, so all indexes have to run backwards 'last'..0

	// Note: prepared data is packed into output point array after removing
	//	redundant data which packs starting into the output array from 0.
	//	As the data is being processed in reverse, the output is then also
	//	in reverse, which affects follow(), as it should follow in the correct
	//	order, so it also goes in reverse

	// Calculate the scale first, as bad scaling factors can mismatch early
	scale = Math::calcSegmentLength
	(	origPoints[last].x,         origPoints[last].y,
		origPoints[last - index].x, origPoints[last - index].y
	);

	// Don't allow actions that would scale up
	if(scale <= zoneScale)
		return false;

	// Normalise scale
	scale = zoneScale / scale;

	// Calculate the angle to rotate by to align the data with the shape
	angle = Math::calcSegmentAngle
	(	origPoints[last].x,         origPoints[last].y,
		origPoints[last - index].x, origPoints[last - index].y
	);

	angle = Math::calcValueDeltaInsideCyclicSet
	(	zoneAngle,
		angle,
		static_cast<float>(Math::PI() + Math::PI())
	);

	// Build transformed points

	points.initialize(origPoints.length());
	points.length() = 0;

	// Position the last movement on top of the last zone
	points[0].x = lastX = static_cast<short>(_zones[_nZones - 1]->_x);
	points[0].y = lastY = static_cast<short>(_zones[_nZones - 1]->_y);
	points.length()++;

	// Prepare the rotate details for the transformation matrix
	cosTheta = cos(angle);
	sinTheta = sin(angle);
	// Reuse 'index' to interate through points
	for(index = 1; index < origPoints.length(); index++)
	{

		// Move to origin
		x = origPoints[last - index].x - origPoints[last].x;
		y = origPoints[last - index].y - origPoints[last].y;

		// Transform matrix (rotate, scale, and translate)
		tformX = static_cast<short>	(	x * cosTheta
									  +	y * sinTheta
									  *	scale
									  +	_zones[_nZones - 1]->_x
									);
		tformY = static_cast<short>	(	x * -sinTheta
									  +	y * cosTheta
									  *	scale
									  +	_zones[_nZones - 1]->_y
									);

		// If this point is now off the shape altogether, then crop
		//	the movement to just what's processed to this point
		// TODO - maybe allow it to go off a little
		if(tformX < 0 || tformY < 0
		|| tformX >= static_cast<short>(_width)
		|| tformY >= static_cast<short>(_nData / _width))
			break;

		// Don't store points if they don't go nowhere
		//	i.e. this point is on the same grid element as the last
		if(tformX != lastX || tformY != lastY)
		{	points[points.length()].x = lastX = tformX;
			points[points.length()].y = lastY = tformY;
			points.length()++;
		}

	}
//cout << index << endl;
//	shapeEditHook(100, points);

	return true;

}

///////////////////////////////////////////////////////////////////////////////
// follow
//
// For each point, trace the line segments of each point to see that they pass
//	through all zones, entering and exiting through the correct angles
//	All zones must be entered in order, but can be exited in any order
//	If a zone fails to exit correctly, all zones entered after and including
//	that zone are considered to have not entered
bool Shape::follow
(	Points &	points
)	const
{	uint		index;
	uint		last		= points.length() - 1;
	ezr *		results;
	uint		zoneIndex;
	uint		goodIndex	= 0;
	uint		exitIndex	= 0;
	uint		cropIndex	= last;
	bool		entering;

	// Must have at least two points to test a movement
	if(points.length() < 2)
		return false;

	// Track how zones are exited. They must be entered in order, but they can
	//	exit in any order so this must be capable of tracking them all
	results = new ezr[_nZones];
	for(zoneIndex = 0; zoneIndex < _nZones; zoneIndex++)
		results[zoneIndex] = ezresult::NOCHANGE;
	zoneIndex = 0;

	// Note: point data runs 0..length as new to old. Follow matches old data
	//	first, runs old to new, so all indexes from from 'last' to 0. points
	//	data is normally run from old to new, but has been reversed by the
	//	packing algorithm in prepare()

	// Run through all points and zones. If all zones were entered
	//	(zoneIndex == _nZones) exit early, the match is complete. Not all
	//	points have to be tested; the last ones are cropped
	for(index = 0; index < points.length() - 1 && zoneIndex < _nZones; index++)
	{

		// Test for enter - enter as many as possible. This may also PASS some
		//	zones and continue entering others, but if any fail, it will be that
		//	zone that doesn't get entered and zoneIndex will remain on it
		entering = true;
		while(zoneIndex < _nZones && entering == true)
		{

			_zones[zoneIndex]->compare
			(	points[last - index].x,
				points[last - index].y,
				points[last - index - 1].x,
				points[last - index - 1].y,
				results[zoneIndex],
				zoneIndex == 0 ? ezmode::INITIALIZE : ezmode::NORMAL
			);

			// When a zone is entered, prepare to test the next zone entered
			if((results[zoneIndex] & ezresult::ENTERED) == ezresult::ENTERED)
			{

				// All points before this are not to be considered as part of the
				//	shape when running the weig test
				if(zoneIndex == 0)
					cropIndex = points.length() - index;

				zoneIndex++;

			}
			else
				entering = false;

		}

		// An exit can be any order, so need to test them all
		//	A goodIndex is set to the lowest known exit complete range
		//	so all before goodIndex are all passed and will never be
		//	considered again during this follow
		for(exitIndex = goodIndex; exitIndex < zoneIndex; exitIndex++)
		{

			// If this result hasn't already completed, test if it's exited
			if(results[exitIndex] != ezresult::PASSED)
			{

				// Test for exit or failure to exit
				_zones[exitIndex]->compare
				(	points[last - index].x,
					points[last - index].y,
					points[last - index - 1].x,
					points[last - index - 1].y,
					results[zoneIndex]
				);

				// If this zone exited incorrectly, fail is result, this zone
				//	now becomes the one being searched for entry, all following
				//	successful entries are implicitly failed too
				if((results[exitIndex] & ezresult::FAILED) == ezresult::FAILED)
				{	zoneIndex = exitIndex;	
					break;
				}

				// After this point, the result will either be ENTERED or
				//	PASSED. ENTERED will be left until next time this loop runs
				//	to try for another PASSED or FAILED, and PASSED will be
				//	removed below (if all before it have passed too)

			}

			// Update the good index to account for all the passed zones
			//	so next inner loop will be a bit shorter
			if(exitIndex == goodIndex)
				if(results[exitIndex] == ezresult::PASSED)
					goodIndex++;

		}

	}

	// All were done successfully if all zones were at least entered; zoneIndex
	//	will only == _nZones if they were all entered. The zones don't have to
	//	have exited to be successful, just entered (so don't need to iterate
	//	through result list to check they all passed)
	if(zoneIndex != _nZones)
		return false;

	// Crop length of points to just those that completed the test
	points.length() = cropIndex;

	return true;

}

///////////////////////////////////////////////////////////////////////////////
// weigh
//
float Shape::weigh
(	Points &	points
)	const
{
	points;
	return 1.0f;
}

}
