#ifndef __INTERPRETER_POINT_H__
#define __INTERPRETER_POINT_H__

#include "../../type.h"

namespace interpreter
{

/**
 * Access the elements of the raw array in Point
 * @see Point
 * @author EB
 * @version 1.0
 */
namespace epoint
{
	/**
	 * Access the x coordinate element (also time)
	 */
	epr const	X	= 0;
	/**
	 * Access the y coordinate element
	 */
	epr const	Y	= 1;
}

/**
 * Structure to hold point data for each frame
 * @author EB
 * @version 1.0
 */
class Point
{

public:
	/**
	 * Track which frame number this point belongs to.
	 * As data is pruned for heuristic match, it needs to be able to relate
	 *	back to the original data for the final orientation and render
	 * @author EB
	 * @version 1.0
	 */
	uint				frame;
	union
	{

		class
		{
		public:
			union
			{	/**
				 * Track the x coordinate (movement)
				 * @author EB
				 * @version 1.0
				 */
				short	x;
				/**
				 * Track the time (speed and accel)
				 * @author EB
				 * @version 1.0
				 */
				short	time;
			};
			/**
			 * Track the y coordinate (movement, speed, and accel)
			 * @author EB
			 * @version 1.0
			 */
			short		y;
		};
		/**
		 * Give array access to each of the elements of the class
		 * @author EB
		 * @version 1.0
		 */
		short			raw		[2];

	};

};

}

#endif
