#ifndef __INTERPRETER_FRAME_H__
#define __INTERPRETER_FRAME_H__

#include "FrameTag.h"

/*
 * Author:	EB
 *
 * Store the position and direction of an IR blob and link to next frame
 *
 */
namespace Interpreter
{

class Frame
{

					// Be friends with Animation so it can set the next frame
	friend			class Animation;

public:
	/**/			Frame
					(	int const			x,
						int const			y,
						int const			size
					);
					// Get the x-coordinate value
	int				x						(void)	const;
					// Get the y-coordinate value
	int				y						(void)	const;
					// Get the x-vector value, calculated by subtracting the x of
					//	the next frame, from the x of this frame
	int				u						(void)	const;
					// Get the y-vector value, calculated by subtracting the y of
					//	the next frame, from the y of this frame
	int				v						(void)	const;
					// Get the size of the IR blob (radius)
	int				size					(void)	const;
					// Get the time this frame was created (set during constructor)
	int				time					(void)	const;
					// Get/Set the associated tagged data
	FrameTag * &	tag						(void);
					// Get the next frame in the animation
	Frame *			next					(void);

private:
					// Set the next frame
	void			next
					(	Frame const * const	next
					);

private:
					// Store the x-coordinate value
	int				_x;
					// Get the y-coordinate value
	int				_y;
					// Get the size of the IR blob (radius)
	int				_size;
					// Get the time this frame was created (set during constructor)
	int				_time;
					// Get/Set the associated tagged data
	FrameTag *		_tag;
					// Store the next frame
	Frame *			_next;

};

}

#endif
