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
// commands
//
public:
	/**
	 * Compare a track against this data.
	 * This must be overloaded to say what track data will be compared against
	 *	and compare(int *, int *) should be called to do the actual comparison
	 * @param track The track to compare against
	 * @param shapeMatches A filter and collection for the matched shapes
	 * @return A weight of how close the track matches the shape from (0..1)
	 * @author EB
	 * @version 1.0
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
					(	float const * const		data,
						uint const				width,
						uint const				nData,
						Zone const * const		zones,
						uint const				nZones
					);

///////////////////////////////////////////////////////////////////////////////
// protected commands
//
protected:
	/**
	 * Test an array of (x, y) points against this data and add it if it's in range
	 * @param points An array of x, y co-ordinates (x1, y1, x2, y2, ..,
	 *	x[length], y[length])
	 * @param length The number of points in the array.
	 * @param shapeMatches A filter and collection for the matched shapes
	 * @author EB
	 * @version 1.0
	 * @pre /length(points) == length * 2;
	 * @pre length > 0;
	 */
	void			test
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
	void			add
					(	float const				weight,
						ShapeMatches * const	shapeMatches
					);

///////////////////////////////////////////////////////////////////////////////
// fields
//
private:
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
	 * Resolution of the shape, or length of _data array. Height is _nData / _width
	 * @author EB
	 * @version 1.0
	 */
	uint const			_nData;
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
(	float const * const	data,
	uint const			width,
	uint const			nData,
	Zone const * const	zones,
	uint const			nZones
) :	_data				(data),
	_width				(width),
	_nData				(nData),
	_zones				(zones),
	_nZones				(nZones)
{ }

}

#endif
