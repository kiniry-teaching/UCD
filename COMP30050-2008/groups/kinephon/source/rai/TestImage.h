#ifndef __INTERPRETER_TESTIMAGE_H__
#define __INTERPRETER_TESTIMAGE_H__

#include "../type.h"

/**
 */
uchar * *	createImage
			(	uint		width,
				uint		height
			);

void		destroyImage
			(	uchar * *	image
			);

bool		writeImage
			(	char const * const	filename,
				uchar * *			image,
				uint				width,
				uint				height
			);

#endif
