#ifndef __INTERPRETER_SHAPESLOADER_H__
#define __INTERPRETER_SHAPESLOADER_H__

#include <fstream>
#include "../../type.h"
#include "Shapes.h"
using std::ifstream;

namespace interpreter
{

namespace etype
{
	/**
	 * The shape loaded describes a movement
	 * @author EB
	 * @version 1.0
	 */
	est const	MOVEMENT	= 0;
	/**
	 * The shape loaded describes a speed
	 * @author EB
	 * @version 1.0
	 */
	est const	SPEED		= 1;
	/**
	 * The shape loaded describes an acceleration
	 * @author EB
	 * @version 1.0
	 */
	est const	ACCEL		= 2;
}

/**
 * Loads all shape data
 * @author EB
 * @version 1.0
 */
class ShapesLoader
{

///////////////////////////////////////////////////////////////////////////////
// commands
//
public:
	/**
	 * Loads all shape data
	 * @param filename Path to shape data file to load
	 * @return Returns a collection of shapes collection with all shapes
	 *	loaded
	 * @author EB
	 * @version 1.0
	 */
	static Shapes *	loadShapes
					(	char const * const	filename
					);

///////////////////////////////////////////////////////////////////////////////
// private commands
//
private:
	/**
	 * Load a single shape.
	 * The file is expected to be in the correct position for reading the
	 *	shape, and the shapes is expected to have enough room to hold it
	 * @param file The file reader to load from
	 * @param shapes The shapes object to load to
	 * @author EB
	 * @version 1.0
	 * @pre file != 0 && shapes != 0;
	 */
	static bool		loadShape
					(	ifstream &			file,
						Shapes *			shapes
					);
	/**
	 * Load a single zone.
	 * The file is expected to be in the correct position for reading the
	 *	shape
	 * @param file The file reader to load from
	 * @param zone Pointer to where the zone's pointer is to be stored
	 * @author EB
	 * @version 1.0
	 * @pre file != 0 && zone != 0;
	 */
	static bool		loadZone
					(	ifstream &			file,
						Zone * &			zone
					);
	/**
	 * Load a shape's data
	 * The file is expected to be in the correct position for reading the
	 *	shape, and the data is expected to have enough room to hold it.
	 *	The file data is converted from uchar to float
	 * @param file The file reader to load from
	 * @param data Array of floats where shape's data is stored
	 * @param nData Length of data
	 * @author EB
	 * @version 1.0
	 * @pre file != 0 && data != 0 && nData != 0;
	 */
	static bool		loadData
					(	ifstream &			file,
						float *				data,
						uint				nData
					);

///////////////////////////////////////////////////////////////////////////////
// file structure
//
private:
	/**
	 * Store the value of the magic id for shape data files
	 * @author EB
	 * @version 1.0
	 */
	static uint const	magic;

///////////////////////////////////////////////////////////////////////////////
// header
//
	/**
	 * File structure - header.
	 * Repeats once
	 * @author EB
	 * @version 1.0
	 */
	class SEHeader
	{
	public:
		/**
		 * Magic id - must be SEV* where * is version number.
		 * @author EB
		 * @version 1.0
		 */
		uint		magic;
		/**
		 * Number of top-level shapes in the file.
		 * This does not count children shapes, which are counted in the
		 *	shape itself
		 * @author EB
		 * @version 1.0
		 */
		uint		nShapes;
	};

///////////////////////////////////////////////////////////////////////////////
// shape
//
	/**
	 * File structure - shape.
	 * Contained in: SEHeader.
	 * Repeats: SEHeader::shapes times + (for each shape) SEShape::shapes
	 *	times.
	 * @author EB
	 * @version 1.0
	 */
	class SEShape
	{
	public:
		/**
		 * Shape type.
		 * Whether this is a movement, speed, or acceleration shape.
		 * @author EB
		 * @version 1.0
		 */
		est			type;
		/**
		 * Shape id.
		 * Globally unique identifier for this shape
		 * @author EB
		 * @version 1.0
		 */
		sid			shapeId;
		/**
		 * Width of this shape's data grid.
		 * Height is calculated by length / width
		 * @author EB
		 * @version 1.0
		 */
		uint		width;
		/**
		 * Length of this shape's data grid.
		 * Number of data bytes in this shape. Height is calculated by
		 *	length / width
		 * @author EB
		 * @version 1.0
		 */
		uint		nData;
		/**
		 * Number of grid elements left and right to bound the test to
		 * 
		 * @author EB
		 * @version 1.0
		 */
		uint		hBound;
		/**
		 * Number of grid elements top and bottom to bound the test to
		 * @author EB
		 * @version 1.0
		 */
		uint		vBound;
		/**
		 * Number of zones in this shape
		 * @author EB
		 * @version 1.0
		 */
		uint		nZones;
		/**
		 * Number of child speed shapes
		 * @author EB
		 * @version 1.0
		 */
		uint		nSpeedShapes;
		/**
		 * Number of child acceleration shapes
		 * @author EB
		 * @version 1.0
		 */
		uint		nAccelShapes;
		/**
		 * Allow start from any zone
		 * @author EB
		 * @version 1.0
		 */
		bool		zoneAnyStart;
		/**
		 * Allow reverse of zone order
		 * @author EB
		 * @version 1.0
		 */
		bool		zoneReverse;
		/**
		 * Pad to 4 byte alignment
		 * @author EB
		 * @version 1.0
		 */
		uchar		padding[2];

	};

///////////////////////////////////////////////////////////////////////////////
// zone
//
	/**
	 * File structure - zone.
	 * Contained in: SEShape.
	 * Repeats: SEShape::zones times per shape.
	 * @author EB
	 * @version 1.0
	 */
	class SEZone
	{
	public:
		/**
		 * Zone's x position
		 * @author EB
		 * @version 1.0
		 */
		float		x;
		/**
		 * Zone's y position
		 * @author EB
		 * @version 1.0
		 */
		float		y;
		/**
		 * Zone's enter radius
		 * @author EB
		 * @version 1.0
		 */
		float		enterRadius;
		/**
		 * Zone's exit radius
		 * @author EB
		 * @version 1.0
		 */
		float		exitRadius;
		/**
		 * Zone's enter angle
		 * @author EB
		 * @version 1.0
		 */
		float		enterAngle;
		/**
		 * Zone's exit angle
		 * @author EB
		 * @version 1.0
		 */
		float		exitAngle;
		/**
		 * Zone's enter arc (angles off enter angle that are valid)
		 * @author EB
		 * @version 1.0
		 */
		float		enterArc;
		/**
		 * Zone's exit arc (angles off exit angle that are valid)
		 * @author EB
		 * @version 1.0
		 */
		float		exitArc;
	};

///////////////////////////////////////////////////////////////////////////////
// data
//
	/**
	 * File structure - data.
	 * Contained in: SEShape.
	 * Repeats: Once per shape.
	 * @author EB
	 * @version 1.0
	 */
	class SEData
	{
	public:
		/**
		 * Data of the zone (SEShape::length in size).
		 * This must be converted to a float normal (0..1) before storing
		 * @author EB
		 * @version 1.0
		 */
		uchar		data;
	};

};

}

#endif
