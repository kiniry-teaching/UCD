#ifdef __TEST__
#include <stdio.h>
#include "TestImage.h"

uchar * * createImage
(	uint		width,
	uint		height
){	uchar * *	image;
	uchar *		data;
	uint		y;

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

#endif
