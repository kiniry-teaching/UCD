#ifndef __INTERPRETER_SHAPESLOADER_H__
#define __INTERPRETER_SHAPESLOADER_H__

#include "Shapes.h"

/*
 * Author:	EB
 *
 * Load each movement shape and its related speed and acceleration shapes
 *
 */
namespace Interpreter
{

class ShapesLoader
{

public:				// Methods
					// Load all shapes from filename
					//	and return a pointer to them
	static Shapes *	loadShapes
					(	char const * const	filename
					);

};

}

#endif
