#ifndef __INTERPRETER_SHAPE_H__
#define __INTERPRETER_SHAPE_H__

#include "../../type.h"
#include "../Recorder/Track.h"
#include "Points.h"
#include "Zone.h"
#include "ShapeMatches.h"

namespace interpreter
{

typedef void			(*SHAPE_EDIT_HOOK)
						(	sid			shapeId,
							Points &	points
						);
extern SHAPE_EDIT_HOOK	shapeEditHook;

/**
 * Store data of a single shape gesture for comparison against a track
 * @author EB
 * @version 1.0
 */
class Shape
{

///////////////////////////////////////////////////////////////////////////////
// friends
//
	/**
	 * Be friends with Shapes so it can destroy this object
	 * @author EB
	 * @version 1.0
	 */
	friend			class Shapes;

#ifdef __TEST__
	/**
	 * Be friends with ShapesLoader so it can test the data is correct
	 * @author EB
	 * @version 1.0
	 */
	friend			class ShapesLoader;
#endif

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
	sid				shapeId							(void)		const;

///////////////////////////////////////////////////////////////////////////////
// commands
//
public:
	/**
	 * Compare a track against this data.
	 * This must be overloaded to say what track data will be compared against
	 *	and compare(Points&) should be called to do the actual comparison
	 * @param track The track to compare against
	 * @param shapeMatches A filter and collection for the matched shapes
	 * @return A true if any match was fould, else false
	 * @author EB
	 * @version 1.0
	 * @pre track != 0 && shapeMatches != 0;
	 * @post \result == true ==> shapeMatches->length() != 0;
	 */
	virtual bool	compare
					(	Track const * const			track,
						ShapeMatches * const		shapeMatches
					)								pure;

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
	 * @param zoneAnyStart Can a match start from any zone, or must it start from zone 0
	 * @param zoneReverse Can a match run through the zones in reverse
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
					(	sid							shapeId,
						float const * const			data,
						uint const					width,
						uint const					nData,
						bool const					zoneAnyStart,
						bool const					zoneReverse,
						Zone const * const * const	zones,
						uint const					nZones
					);
	/**
	 * Destroy a shape
	 */
	virtual			~Shape							(void);

///////////////////////////////////////////////////////////////////////////////
// protected commands
//
protected:
	/**
	 * Compare points against this data and add it if it's in range
	 * @param origPoints Original collection of points. An unoriginal version
	 *	will be created to rotate and scale repeatedly until a match is found
	 * @param shapeMatches A filter and collection for the matched shapes
	 * @return The shape match with the weight of how close the match was
	 *	or 0 if no match was made
	 * @author EB
	 * @version 1.0
	 */
	ShapeMatch *	compare
					(	Points &					origPoints,
						ShapeMatches * const		shapeMatches
					)	const;

///////////////////////////////////////////////////////////////////////////////
// private commands
//
private:
	/**
	 * Prepare the original data by rotating, scaling, and cropping it.
	 * @param origPoints The original point data
	 * @param points The point data rotated, scaled, and cropped
	 * @param index The first point to match against the first zone. Decides
	 *	angle and scaling
	 * @param angle [out] Get the angle used
	 * @param scale [out] Get the scale used
	 * @param zoneAngle Precalculated angle of the first zone to the second
	 * @param zoneScale Precalculated scale of the first zone to the second
	 * @returns true if the data is usable
	 * @author EB
	 * @version 1.0
	 * @post points.length() <= origPoints.length();
	 */
	bool			prepare
					(	Points &					origPoints,
						Points &					points,
						uint						index,
						float &						angle,
						float &						scale,
						float						zoneAngle,
						float						zoneScale
					)	const;
	/**
	 * Trace the prepared points to make sure they pass through all the zones.
	 * @param points The prepared point data
	 * @returns true if all zones were passed in the correct order and angle
	 * @author EB
	 * @version 1.0
	 */
	bool			follow
					(	Points &					points
					)	const;
	/**
	 * Get a weight of how close the point data matches the shape data
	 * @param points The prepared and followed point data
	 * @returns A value from 0 to 1 of how close the point data matches the
	 *	shape data, with 0 meaning no match, and 1 is perfect match
	 * @author EB
	 * @version 1.0
	 * @post /result >= 0.0f && /result <= 1.0f;
	 */
	float			weigh
					(	Points &					points
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
					(	float const					weight,
						ShapeMatches * const		shapeMatches
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
	sid const					_shapeId;
	/**
	 * Flat 2 dimensional array of weights in the range (0..1) describing this
	 *	shape. Positions containing a 1 are points in the shape, 0, points not
	 *	in the shape
	 * @author EB
	 * @version 1.0
	 */
	float const * const			_data;
	/**
	 * Width of the shape. Height is _nData / _width
	 * @author EB
	 * @version 1.0
	 */
	uint const					_width;
	/**
	 * Resolution of the shape, or length of _data array. Height is
	 *	_nData / _width
	 * @author EB
	 * @version 1.0
	 */
	uint const					_nData;
	/**
	 * State whether any zone in this shape can be a start zone
	 * If false, the gesture must start and the 0th order zone
	 *	Allowing any zone will slow things down as each zone will have to be
	 *	tested to see if it's a potential start zone
	 * @author EB
	 * @version 1.0
	 */
	bool const					_zoneAnyStart;
	/**
	 * State whether the zone orders can be reversed
	 * As well as reversing the order of the zones, this also swaps the
	 *	enter/exit angle/arc of each zone. It does not affect the enter/exit
	 *	radius. Allowing zone reverse will slow things down as the zones have
	 *	to be reversed and tested against to see if it's a potential match
	 * @author EB
	 * @version 1.0
	 */
	bool const					_zoneReverse;
	/**
	 * Array of zones in this shape.
	 * Zones are areas that must be entered and exited in a particular order
	 *	for the shape to match
	 * @author EB
	 * @version 1.0
	 */
	Zone const * const * const	_zones;
	/**
	 * Length of the zones array.
	 * @author EB
	 * @version 1.0
	 */
	uint const					_nZones;

};

///////////////////////////////////////////////////////////////////////////////

inline Shape::Shape
(	sid							shapeId,
	float const * const			data,
	uint const					width,
	uint const					nData,
	bool const					zoneAnyStart,
	bool const					zoneReverse,
	Zone const * const * const	zones,
	uint const					nZones
) :	_shapeId					(shapeId),
	_data						(data),
	_width						(width),
	_nData						(nData),
	_zoneAnyStart				(zoneAnyStart),
	_zoneReverse				(zoneReverse),
	_zones						(zones),
	_nZones						(nZones)
{ }

inline Shape::~Shape(void)
{	uint	index;

	delete [] const_cast<float *>(_data);

	// Though the ShapeLoader created the zone object,
	//	because it is internal in the Analyser, don't
	//	bother get the ShapeLoader to destroy it, both
	//	are guaranteed to operate on the same heap
	for(index = 0; index < _nZones; index++)
		delete const_cast<Zone *>(*(_zones + index));
	delete [] const_cast<Zone * *>(_zones);

}

inline sid Shape::shapeId(void) const
{	return _shapeId;
}

}

#endif
