#ifndef __INTERPRETER_SHAPE_H__
#define __INTERPRETER_SHAPE_H__

#include "Track.h"

namespace interpreter
{

/**
 * Store data of a single shape gesture for comparison against a track
 * @author EB
 * @version 1.0
 */
class Shape
{

	/**
	 * Be friends with ShapesLoader so it can modify the shape's data
	 * @author EB
	 * @version 1.0
	 */
	friend			class ShapesLoader;

protected:
	/**
	 * Create a shape.
	 * The shape's data is filled by the ShapeLoader
	 * @param data Array of weight map data describing this shape
	 * @param width The width of the 2 dimensional weight map
	 * @param nData The resolution of the weight map (height is nData / width)
	 * @param zones Array of zones in this shape
	 * @param zones Total number of zones
	 * @author EB
	 * @version 1.0
	 * @pre data != 0;
	 * @pre width > 0;
	 * @pre nData > 0;
	 * @pre nData % width == 0;
	 * @pre nZones >= 0;
	 */
					Shape
					(	float const * const	data,
						uint const			width,
						uint const			nData,
						Zone const * const	zones,
						uint const			nZones
					);
	/**
	 * Destroy this shape
	 * @author EB
	 * @version 1.0
	 */
	virtual			~Shape					(void);

public:
	/**
	 * Compare a track against this data.
	 * This must be overloaded to say what track data will be compared against
	 *	and compare(int *, int *) should be called to do the actual comparison
	 * @param track The track to compare against
	 * @return A weight of how close the track matches the shape from (0..1)
	 * @author EB
	 * @version 1.0
	 */
	virtual float	compare
					(	Track const * const	track
					)	const				pure;

private:
	/**
	 * Compare an array of (x, y) points against this data.
	 * @param x An array of x co-ordinates
	 * @param y An array of y co-ordinates
	 * @param length The size of the x and y arrays
	 * @return A weight from (0..1) of how close the (x, y) array matches the
	 *	shape
	 * @author EB
	 * @version 1.0
	 * @pre /length(x) == /length(y) == length;
	 * @pre length > 0;
	 */
	float			compare
					(	int const * const	x,
						int const * const	y,
						uint const			length
					)	const;

private:
	/**
	 * Flat 2 dimensional array of weights in the range (0..1) describing this
	 *	shape. Positions containing a 1 are points in the shape, 0, points not
	 *	in the shape
	 * @author EB
	 * @version 1.0
	 */
	float *			_data;
	/**
	 * Width of the shape. Height is _nData / _width
	 * @author EB
	 * @version 1.0
	 */
	uint			_width;
	/**
	 * Resolution of the shape, or length of _data array. Height is _nData / _width
	 * @author EB
	 * @version 1.0
	 */
	uint			_nData;
	/**
	 * Array of zones in this shape.
	 * Zones are areas that must be entered and exited in a particular order
	 *	for the shape to match
	 * @author EB
	 * @version 1.0
	 */
	Zone *			_zones;
	/**
	 * Length of the zones array.
	 * @author EB
	 * @version 1.0
	 */
	uint			_nZones;

};

}

#endif
