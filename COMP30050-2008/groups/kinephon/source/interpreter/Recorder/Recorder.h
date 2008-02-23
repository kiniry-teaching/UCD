#ifndef __INTERPRETER_RECORDER_H__
#define __INTERPRETER_RECORDER_H__

#include "Animation.h"

/*
 * Author:	EB
 *
 * Record each blobs movements
 *
 */
namespace Interpreter
{

class Recorder
{

public:
	/**/		Recorder		(void);
				// Get the number of blobs being recorded
	int			length			(void)	const;

				// Return an animation by blob id
	Animation *	operator []
				(	int const	id
				)	const;

private:
				// Array of animations
	Animation *	_animations;

};

}

#endif
