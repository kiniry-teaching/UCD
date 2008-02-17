#ifndef __INTERPRETER_SHAPE_H__
#define __INTERPRETER_SHAPE_H__

#include "Animation.h"

/*
 * Author:	EB
 *
 * Store the approximation of a shape to be compared against a movement
 *
 */
namespace Interpreter
{

class Shape
{

public:				// Constructor
					// Load the <name>'d shape data 
	/**/			Shape
					(	char const * const		name
					);
	virtual			~Shape						(void);

public:				// Methods
					// Comare an animation against this shape
					//	Overload to compare movements, speeds, or accelerations
	virtual float	compare
					(	Animation const * const	animation
					)	const;

private:
					// Compare array of vector points against the shape data	
	float			compare
					(	int const * const		x,
						int const * const		y
					);

private:
					// 2 dimensional array of shape compare data
	float *			_array;
					// Width of array (height = _length / _width)
	int				_width;
					// Total length of array
	int				_length;
					// Array of sub-shapes describing speeds
	Shape *			_shapeSpeed;
					// Array of sub-shapes describing accelerations
	Shape *			_shapeAcceleration;
					// Elemements in _shapeSpeed
	int				_lengthSpeed;
					// Elemements in _shapeAcceleration
	int				_lengthAcceleration;

};

}

#endif
