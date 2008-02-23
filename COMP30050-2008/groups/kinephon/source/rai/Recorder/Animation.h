#ifndef __INTERPRETER_ANIMATION_H__
#define __INTERPRETER_ANIMATION_H__

#include "Frame.h"

/*
 * Author:	EB
 *
 * Store all the frames for a single IR blob
 *
 */
namespace Interpreter
{

class Animation
{

				// Be friends with Recorder so it can add frames
	friend		class Recorder;

public:
	/**/		Animation
				(	int const	id
				);
	virtual		~Animation		(void);
				// Get the id of the blob that this animation records
	int			id				(void)	const;
				// Get the number of frames
	int			length			(void)	const;
				// Get the first frame in the list of frames
	Frame *		frames			(void)	const;

				// Return a frame by index
	Frame *		operator []
				(	int const	index
				)	const;

private:
				// Add the next frame to the end of the list
	void		next
				(	Frame const * const	next
				);

private:
				// Store the id of the blob that this animation records
	int			_id;
				// First in linked list of frames in animation
	Frame *		_frameFirst;
				// Last in linked list of frames in animation, for quick add
	Frame *		_frameLast;

};

}

#endif
