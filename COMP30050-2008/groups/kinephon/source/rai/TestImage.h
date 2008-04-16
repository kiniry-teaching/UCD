#ifndef __INTERPRETER_TESTIMAGE_H__
#define __INTERPRETER_TESTIMAGE_H__

#include "../type.h"

/**
 * Create a two dimensional array of bytes.
 * Array should be accessed using coordinates as image[y][x]. It can also be
 *	accessed as a one dimensional array using image[0][i]
 * @param width The number of elements along the x coordinate
 * @param height The number of elements along the y coordinate
 * @returns Pointer to array of pointers to y offsets in image memory block
 * @author EB
 * @version 1.0
 */
uchar * *	createImage
			(	uint				width,
				uint				height
			);
/**
 * Destory an image created with createImage()
 * @param image The image pointer returned by createImage()
 * @author EB
 * @version 1.0
 */
void		destroyImage
			(	uchar * *			image
			);
/**
 * Write an image to disk
 * @param filename The file to write to. Must include the extension .pgm
 * @param image The image pointer returned by createImage()
 * @param width The width of the image. This must match the width passed to
 *	createImage when image was created
 * @param height The height of the image. This must match the height passed
 *	to createImage when image was created
 * @author EB
 * @version 1.0
 */
bool		writeImage
			(	char const * const	filename,
				uchar * *			image,
				uint				width,
				uint				height
			);

#endif
