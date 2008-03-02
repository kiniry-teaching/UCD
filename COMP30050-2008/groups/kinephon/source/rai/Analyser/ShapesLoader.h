#ifndef __INTERPRETER_SHAPESLOADER_H__
#define __INTERPRETER_SHAPESLOADER_H__

#include "Shapes.h"

namespace interpreter
{

/**
 * Loads all shape data
 * @author EB
 * @version 1.0
 */
class ShapesLoader
{

public:
	/**
	 * Loads all shape data
	 * @param filename Path to shape data file to load
	 * @return Returns a collection of shapes collection with all shapes loaded
	 * @author EB
	 * @version 1.0
	 */
	static Shapes *	loadShapes
					(	char const * const	filename
					);

};

}

#endif
