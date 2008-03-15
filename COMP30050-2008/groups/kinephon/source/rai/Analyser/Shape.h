#ifndef __INTERPRETER_SHAPE_H__
#define __INTERPRETER_SHAPE_H__

#include "../../type.h"
#include "../Recorder/Track.h"
#include "Zone.h"
#include "ShapeMatches.h"

namespace interpreter
{

/**
 * Store data of a single shape gesture for comparison against a track
 * @author EB
 * @version 1.0
 */
class Shape
{

///////////////////////////////////////////////////////////////////////////////
// queries
//
public:
	/**
	 * The identifier set for this shape in the shape editor
	 * @return the identifier set for this shape in the shape editor
	 * @author EB
	 * @version 1.0
	 */
	sid				shapeId						(void)		const;

///////////////////////////////////////////////////////////////////////////////
// commands
//
public:
	/**
	 * Compare a track against this data.
	 * This must be overloaded to say what track data will be compared against
	 *	and compare(int *, int *) should be called to do the actual comparison
	 * @param track The track to compare against
	 * @param shapeMatches A filter and collection for the matched shapes
	 * @return A true if any match was fould, else false
	 * @author EB
	 * @version 1.0
	 * @pre track != 0 && shapeMatches != 0;
	 * @post \result == true ==> shapeMatches->length() != 0;
	 */
	virtual bool	compare
					(	Track const * const		track,
						ShapeMatches * const	shapeMatches
					)							pure;

///////////////////////////////////////////////////////////////////////////////
// *tor
//
protected:
	/**
	 * Create a shape.
	 * The shape's data is filled by the ShapeLoader
	 * @param shapeId A unique identifier for this shape
	 * @param data Array of weight map data describing this shape
	 * @param width The width of the 2 dimensional weight map
	 * @param nData The resolution of the weight map (height is nData / width)
	 * @param zones Array of zones in this shape
	 * @param nZones Total number of zones
	 * @author EB
	 * @version 1.0
	 * @pre data != 0;
	 * @pre width > 0;
	 * @pre nData > 0;
	 * @pre nData % width == 0;
	 * @pre nZones >= 0;
	 */
					Shape
					(	sid						shapeId,
						float const * const		data,
						uint const				width,
						uint const				nData,
						bool const				zoneAnyStart,
						bool const				zoneReverse,
						Zone const * const		zones,
						uint const				nZones
					);

///////////////////////////////////////////////////////////////////////////////
// protected commands
//
protected:
	/**
	 * Test an array of (x, y) points against this data and add it if it's
	 *	in range
	 * @param points An array of x, y co-ordinates (x1, y1, x2, y2, ..,
	 *	x[length], y[length])
	 * @param length The number of points in the array.
	 * @param shapeMatches A filter and collection for the matched shapes
	 * @author EB
	 * @version 1.0
	 * @pre /length(points) == length * 2;
	 * @pre length > 0;
	 */
	ShapeMatch *	test
					(	int const * const		points,
						uint const				length,
						ShapeMatches * const	shapeMatches
					);

///////////////////////////////////////////////////////////////////////////////
// private commands
//
private:
	/**
	 * Compare an array of (x, y) points against this data.
	 * @param points An array of x, y co-ordinates (x1, y1, x2, y2, ..,
	 *	x[length], y[length])
	 * @param length The number of points in the array.
	 * @return A weight from (0..1) of how close the (x, y) array matches the
	 *	shape
	 * @author EB
	 * @version 1.0
	 * @pre /length(points) == length * 2;
	 * @pre length > 0;
	 */
	float			compare
					(	int const * const		points,
						uint const				length
					)	const;
	/**
	 * Add this to shapeMatches
	 * @param weight The weight by which this shape matched
	 * @param shapeMatches The ShapeMatches to add this to
	 * @author EB
	 * @version 1.0
	 * @pre shapeMatches != 0;
	 */
	ShapeMatch * 	add
					(	float const				weight,
						ShapeMatches * const	shapeMatches
					);

///////////////////////////////////////////////////////////////////////////////
// fields
//
private:
	/**
	 * Identifier set for this shape in the shape editor
	 * @author EB
	 * @version 1.0
	 */
	sid const			_shapeId;
	/**
	 * Flat 2 dimensional array of weights in the range (0..1) describing this
	 *	shape. Positions containing a 1 are points in the shape, 0, points not
	 *	in the shape
	 * @author EB
	 * @version 1.0
	 */
	float const * const	_data;
	/**
	 * Width of the shape. Height is _nData / _width
	 * @author EB
	 * @version 1.0
	 */
	uint const			_width;
	/**
	 * Resolution of the shape, or length of _data array. Height is
	 *	_nData / _width
	 * @author EB
	 * @version 1.0
	 */
	uint const			_nData;
	/**
	 * State whether any zone in this shape can be a start zone
	 * If false, the gesture must start and the 0th order zone
	 *	Allowing any zone will slow things down as each zone will have to be
	 *	tested to see if it's a potential start zone
	 * @author EB
	 * @version 1.0
	 */
	bool const			_zoneAnyStart;
	/**
	 * State whether the zone orders can be reversed
	 * As well as reversing the order of the zones, this also swaps the
	 *	enter/exit angle/arc of each zone. It does not affect the enter/exit
	 *	radius. Allowing zone reverse will slow things down as the zones have
	 *	to be reversed and tested against to see if it's a potential match
	 * @author EB
	 * @version 1.0
	 */
	bool const			_zoneReverse;
	/**
	 * Array of zones in this shape.
	 * Zones are areas that must be entered and exited in a particular order
	 *	for the shape to match
	 * @author EB
	 * @version 1.0
	 */
	Zone const * const	_zones;
	/**
	 * Length of the zones array.
	 * @author EB
	 * @version 1.0
	 */
	uint const			_nZones;

};

///////////////////////////////////////////////////////////////////////////////

inline Shape::Shape
(	sid					shapeId,
	float const * const	data,
	uint const			width,
	uint const			nData,
	bool const			zoneAnyStart,
	bool const			zoneReverse,
	Zone const * const	zones,
	uint const			nZones
) :	_shapeId			(shapeId),
	_data				(data),
	_width				(width),
	_nData				(nData),
	_zoneAnyStart		(zoneAnyStart),
	_zoneReverse		(zoneReverse),
	_zones				(zones),
	_nZones				(nZones)
{ }

inline sid Shape::shapeId(void) const
{	return _shapeId;
}

}

#endif
