#ifdef __TEST__
#include <cassert>
#include <cmath>
#include "ShapeMovement.h"
#include "ShapesLoader.h"
#include "../TestMemory.h"
using std::cout;
using std::endl;

namespace interpreter
{

uchar * * createImage
(	uint		width,
	uint		height
){	uchar * *	image;
	uchar *		data;
	int			y;

	data = new uchar[width * height];
	image = new uchar*[height];

	for(y = 0; y < height; y++)
		image[y] = data + y * width;

	return image;

}

void destroyImage
(	uchar * *	image
){

	delete [] image[0];
	delete [] image;

}

bool writeImage
(	char const * const	filename,
	uchar * *			image,
	uint				width,
	uint				height
){	FILE *				file;
	uint				y;
	uint				x;

	file = (FILE*)fopen(filename, "w");

	if(file == NULL)
		return false;

	fprintf(file, "P2\n");
	fprintf
	(	file,
		"%d %d\n",
			width,
			height
	);
	fprintf(file, "255\n");

	for(y = 0; y < height; y++)
	for(x = 0; x < width; x++)
		fprintf(file, "%d%c", image[y][x], (x == width - 1 ? '\n' : ' '));

	fprintf(file, "\n");

	fclose(file);

	return true;

}

void ShapesLoader::drawImageFromShape
(	Shape *	shape,
	uint	index,
	char	detail,		//= '\0'
	uint	sindex		//= -1
){	char	filename[256];
	uint	i;
	uint	y;
	uint	x;
	uint	width		= shape->_width * 8;
	uint	height		= shape->_nData / shape->_width * 8;

	::stage++; uchar * * image = createImage(width, height);

	::stage++;
	if(sindex == -1)
		sprintf
		(	filename,
			"C:\\Data\\College\\COMP30050 - Software Engerineering Project III\\kinephon\\source\\rai\\Analyser\\TestShapesLoader\\%ld.pgm",
			index
		);
	else
		sprintf
		(	filename,
			"C:\\Data\\College\\COMP30050 - Software Engerineering Project III\\kinephon\\source\\rai\\Analyser\\TestShapesLoader\\%ld%c%ld.pgm",
			index,
			detail,
			sindex
		);

	for(i = 0; i < shape->_nData; i++)
		for(y = 0; y < 8; y++)
		for(x = 0; x < 8; x++)
			image[y + (i / shape->_width) * 8][x + (i % shape->_width) * 8] = shape->_data[i] * 127 + 64;

	for(i = 0; i < shape->_nZones; i++)
	{
		
		Zone const * const zone = shape->_zones[i];
		float a;

		for(a = 0; a < 6.2831853; a += 0.05f)
		{	x = (int)(zone->_x * 8 + cos(a) * zone->_exitRadius * 8);
			y = (int)(zone->_y * 8 + sin(a) * zone->_exitRadius * 8);
			if(x >= 0 && y >= 0 && x < width && y < height)
				image[y][x] = 0;
		}

		for(a = 0; a < 1.0f; a += 0.01f)
		{	x = (int)(zone->_x * 8 + cos(zone->_exitAngle + zone->_exitArc) * zone->_exitRadius * 8 * a);
			y = (int)(zone->_y * 8 + sin(zone->_exitAngle + zone->_exitArc) * zone->_exitRadius * 8 * a);
			if(x >= 0 && y >= 0 && x < width && y < height)
				image[y][x] = 0;
			x = (int)(zone->_x * 8 + cos(zone->_exitAngle - zone->_exitArc) * zone->_exitRadius * 8 * a);
			y = (int)(zone->_y * 8 + sin(zone->_exitAngle - zone->_exitArc) * zone->_exitRadius * 8 * a);
			if(x >= 0 && y >= 0 && x < width && y < height)
				image[y][x] = 0;
		}

		for(a = 0; a < 6.2831853; a += 0.05f)
		{	x = (int)(zone->_x * 8 + cos(a) * zone->_enterRadius * 8);
			y = (int)(zone->_y * 8 + sin(a) * zone->_enterRadius * 8);
			if(x >= 0 && y >= 0 && x < width && y < height)
				image[y][x] = 255;
		}

		for(a = 0; a < 1.0f; a += 0.01f)
		{	x = (int)(zone->_x * 8 + cos(zone->_enterAngle + zone->_enterArc) * zone->_enterRadius * 8 * a);
			y = (int)(zone->_y * 8 + sin(zone->_enterAngle + zone->_enterArc) * zone->_enterRadius * 8 * a);
			if(x >= 0 && y >= 0 && x < width && y < height)
				image[y][x] = 255;
			x = (int)(zone->_x * 8 + cos(zone->_enterAngle - zone->_enterArc) * zone->_enterRadius * 8 * a);
			y = (int)(zone->_y * 8 + sin(zone->_enterAngle - zone->_enterArc) * zone->_enterRadius * 8 * a);
			if(x >= 0 && y >= 0 && x < width && y < height)
				image[y][x] = 255;
		}

		for(x = -1; x < i; x++)
			image[(int)(zone->_y * 8)][(int)(zone->_x * 8) + x] = 255;

	}

	::stage++; writeImage(filename, image, width, height);

	::stage++; destroyImage(image);

}

void ShapesLoader::RunTest(void)
{

	cout << "Running ShapesLoader tests.. ";
	{

	::stage++; Shapes * shapes = ShapesLoader::loadShapes("C:\\Data\\College\\COMP30050 - Software Engerineering Project III\\kinephon\\source\\rai\\kinephon.sec");
	::stage++; int index;
	::stage++; int indexMove;
	::stage++; ShapeMovement * shapeMovement;

	for(index = 0; index < shapes->_shapeIndex; index++)
	{

		drawImageFromShape(shapes->_shapes[index], index);

//		if((shapeMovement = dynamic_cast<ShapeMovement*>(shapes->_shapes[index])) != 0)

		shapeMovement = (ShapeMovement*)shapes->_shapes[index];
		
		{

			if(shapeMovement->_speedShapes != 0)
				for(indexMove = 0; indexMove < shapeMovement->_speedShapes->_shapeIndex; indexMove++)
					drawImageFromShape(shapeMovement->_speedShapes->_shapes[indexMove], index, 's', indexMove);

			if(shapeMovement->_accelShapes != 0)
				for(indexMove = 0; indexMove < shapeMovement->_accelShapes->_shapeIndex; indexMove++)
					drawImageFromShape(shapeMovement->_accelShapes->_shapes[indexMove], index, 'a', indexMove);

		}

	}

	delete shapes;

	::stage = -1;
	cout << "Done" << endl;

	}
	dumpMemoryReport();

}

}

#endif