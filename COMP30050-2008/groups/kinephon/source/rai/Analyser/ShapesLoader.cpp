#include "shapesloader.h"
#include "zone.h"
#include "shapemovement.h"
#include "shapespeed.h"
#include "shapeaccel.h"

namespace interpreter
{

// @todo - is __BIG_ENDIAN__ a common preprocessor directive?
#ifdef __BIG_ENDIAN__
	uint const ShapesLoader::magic = 'SEV1';
#else
	uint const ShapesLoader::magic = '1VES';
#endif

///////////////////////////////////////////////////////////////////////////////
// load all shape data
//
Shapes * ShapesLoader::loadShapes
(	char const * const	filename
){	ifstream			file		(filename, std::ios::binary);
	SEHeader			seHeader;
	uint				index;
	Shapes *			shapes;

	if(file.good() == false)
		return 0;

	// Read the header
	file.read((char*)&seHeader, sizeof(seHeader));
	int x= file.gcount();

	// Don't continue if the filetype
	//	is wrong, or there's no shape data
	if(seHeader.magic != magic
	|| seHeader.nShapes == 0)
		return 0;

	shapes = new Shapes(seHeader.nShapes);

	// Load in each shape. Exit if there's an error
	for(index = 0; index < seHeader.nShapes; index++)
		if(loadShape(file, shapes) == false)
			break;

	file.close();

	// Error, destory all shapes and exit
	if(index != seHeader.nShapes)
	{	delete shapes;
		shapes = 0;
	}

	return shapes;

}

///////////////////////////////////////////////////////////////////////////////
// load shape
//
bool ShapesLoader::loadShape
(	ifstream &	file,
	Shapes *	shapes
){	SEShape		seShape;
	uint		index;
	Shape *		shape;
	float *		data;
	Zone * *	zones			= 0;
	Shapes *	speedShapes		= 0;
	Shapes *	accelShapes		= 0;
	bool		success			= true;

	//-------------------------------------------------------------------------
	// Read the shape header

	file.read((char*)&seShape, sizeof(seShape));
	if(file.good() == false)
		return false;

	//-------------------------------------------------------------------------
	// Validate as much as possible

	// Error, no data
	if(seShape.nData == 0)
		return false;

	// Error, invalid width
	if(seShape.width == 0
	|| seShape.nData % seShape.width != 0)
		return false;

	// Error, unknown type
	switch(seShape.type)
	{

		// If it's a movement, it's ok
		case etype::MOVEMENT:
			break;

		// If it's a speed or accel, it cannot have children
		case etype::SPEED:
		case etype::ACCEL:
			if(seShape.nSpeedShapes != 0
			|| seShape.nAccelShapes != 0)
				return false;
			break;

		// Otherwise it's unknown, which is an error
		default:
			return false;

	}

	// Don't return false after this point, intead use Success = false;
	//	Memory is only cleaned at the bottom of the function

	//-------------------------------------------------------------------------
	// Allocate memory

	if(seShape.nZones != 0)
		zones = new Zone*[seShape.nZones];

	data = new float[seShape.nData];

	if(seShape.nSpeedShapes != 0)
		speedShapes = new Shapes(seShape.nSpeedShapes);

	if(seShape.nAccelShapes != 0)
		accelShapes = new Shapes(seShape.nAccelShapes);

	//-------------------------------------------------------------------------
	// Load shape's data

	//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
	// Load zones

	for
	(	index = 0;
		index < seShape.nZones
	 &&	success == true;
		index++
	)	if(loadZone(file, *(zones + index)) == false)
			success = false;

	//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
	// Load shape data

	if(success == true)
		success = loadData(file, data, seShape.nData);

	//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
	// Load speed shapes

	for
	(	index = 0;
		index < seShape.nSpeedShapes
	 &&	success == true;
		index++
	)	if(loadShape(file, speedShapes) == false)
			success = false;

	//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
	// Load accel shapes

	for
	(	index = 0;
		index < seShape.nAccelShapes
	 &&	success == true;
		index++
	)	if(loadShape(file, accelShapes) == false)
			success = false;

	//-------------------------------------------------------------------------
	// Finished loading this shape, store it if all ok, else clean up

	if(success == true)
	{

		// Create the required shape
		switch(seShape.type)
		{

			case etype::MOVEMENT:
				shape = new ShapeMovement
				(	seShape.shapeId,
					data,
					seShape.width,
					seShape.nData,
					seShape.zoneAnyStart,
					seShape.zoneReverse,
					zones,
					seShape.nZones,
					speedShapes,
					accelShapes
				);
				break;

			case etype::SPEED:
				shape = new ShapeSpeed
				(	seShape.shapeId,
					data,
					seShape.width,
					seShape.nData,
					seShape.zoneAnyStart,
					seShape.zoneReverse,
					zones,
					seShape.nZones
				);
				break;

			case etype::ACCEL:
				shape = new ShapeAccel
				(	seShape.shapeId,
					data,
					seShape.width,
					seShape.nData,
					seShape.zoneAnyStart,
					seShape.zoneReverse,
					zones,
					seShape.nZones
				);
				break;

		}

		// Store it
		(*shapes) += shape;

	}
	else
	// Failure, clean up
	{

		delete accelShapes;
		delete speedShapes;
		delete [] data;
		delete [] zones;

	}

	return success;

}

///////////////////////////////////////////////////////////////////////////////
// load zone
//
bool ShapesLoader::loadZone
(	ifstream &	file,
	Zone * &	zone
){	SEZone		seZone;

	file.read((char*)&seZone, sizeof(seZone));
	int x= file.gcount();

	zone = new Zone
	(	seZone.x,
		seZone.y,
		seZone.enterRadius,
		seZone.exitRadius,
		seZone.enterAngle,
		seZone.exitAngle,
		seZone.enterArc,
		seZone.exitArc
	);

	return file.good() != false;

}

///////////////////////////////////////////////////////////////////////////////
// load data
//
bool ShapesLoader::loadData
(	ifstream &	file,
	float *		data,
	uint		nData
){	SEData *	seData;
	uint		index;

	seData = new SEData[nData];

	file.read((char*)seData, sizeof(seData->data) * nData);

	for(index = 0; index < nData; index++)
		*(data + index) = (float)(seData + index)->data / 255;

	delete [] seData;

	return file.good() != false;

}

}
