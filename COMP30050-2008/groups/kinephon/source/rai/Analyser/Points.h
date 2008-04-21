#ifndef __INTERPRETER_POINTS_H__
#define __INTERPRETER_POINTS_H__

#include "../../type.h"
#include "Point.h"

namespace interpreter
{

/**
 * Which side of sharp angle should be removed
 * @see Math::calcSharpLineArray()
 * @author EB
 * @version 1.0
 */
namespace eprune
{
	/**
	 * Prune edges inside a given angle
	 */
	esp const	INNER	= false;
	/**
	 * Prune edges outside a given angle
	 */
	esp const	OUTER	= true;
}

/**
 * Structure to hold points data for each frame
 * @author EB
 * @version 1.0
 */
class Points
{

///////////////////////////////////////////////////////////////////////////////
// friends
//
	/**
	 * Be friends with Shape so it can create this object
	 * @author EB
	 * @version 1.0
	 */
	friend	class Shape;
	/**
	 * Be friends with ShapeMovement so it can create this object
	 * @author EB
	 * @version 1.0
	 */
	friend	class ShapeMovement;
	/**
	 * Be friends with ShapeSpeed so it can create this object
	 * @author EB
	 * @version 1.0
	 */
	friend	class ShapeSpeed;
	/**
	 * Be friends with ShapeAccel so it can create this object
	 * @author EB
	 * @version 1.0
	 */
	friend	class ShapeAccel;

///////////////////////////////////////////////////////////////////////////////
// queries
//
public:
	/**
	 * Number of points in the collection
	 * @returns The number of points in the collection
	 * @author EB
	 * @version 1.0
	 */
	uint &	length			(void);
	/**
	 * Get a point by index
	 * @param index The index of the point to get
	 * @returns The point refered to by index
	 * @author EB
	 * @version 1.0
	 * @pre index < length();
	 */
	Point &	operator []
			(	uint		index
			);

///////////////////////////////////////////////////////////////////////////////
// commands
//
public:
	/**
	 * Initialise the points collection to a particular length
	 * @param length Total number of points to create
	 * @author EB
	 * @version 1.0
	 * @pre length > 0;
	 */
	void	initialize
			(	uint		length
			);
	/**
	 * Given an array of (x, y) points, smooth them to remove spikes in the
	 *	data
	 * @param range The number of points either side of a point to smooth
	 *	across
	 * @param affect Affect the x coordinte epoint::X or the Y coordinate
	 *	epoint::Y
	 * @author EB
	 * @version 1.0
	 * @pre affect == 0 || affect == 1;
	 */
	void	smoothen
			(	uchar const	range,
				epr const	affect
			);
	/**
	 * Given an array of (x, y) points, sharpen or unsharpen edges of lines.
	 * @param angle The minimum allowable angle between line segments in the
	 *	output
	 * @param prune Which side of angle should be prunded. ssp::INNER sharpens
	 *	line array. ssp::OUTER removes sharp edges
	 * @author EB
	 * @version 1.0
	 */
	void	sharpen
			(	float const	angle,
				esp const	prune	= eprune::INNER
			);

///////////////////////////////////////////////////////////////////////////////
// private *tor
//
private:
	/**
	 * Create a new point collection
	 * @author EB
	 * @version 1.0
	 */
			Points			(void);
	/**
	 * Destroy point collection and all its points
	 * @author EB
	 * @version 1.0
	 */
			~Points			(void);

///////////////////////////////////////////////////////////////////////////////
// fields
//
private:
	/**
	 * Array of point objects
	 * @author EB
	 * @version 1.0
	 */
	Point *	_points;
	/**
	 * Used elements in array
	 * @author EB
	 * @version 1.0
	 */
	uint	_length;

};

///////////////////////////////////////////////////////////////////////////////

inline Points::Points(void)
 :	_points	(0),
	_length	(0)
{ }

inline Points::~Points(void)
{	delete _points;
}

inline void Points::initialize
(	uint length
){	delete [] _points;
	_points = new Point[_length = length];
}

inline uint & Points::length(void)
{	return _length;
}

inline Point & Points::operator []
(	uint	index
){	return _points[index];
}

}

#endif
