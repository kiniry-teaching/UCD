#ifndef __INTERPRETER_FRAME_H__
#define __INTERPRETER_FRAME_H__

#include "../../type.h"

namespace interpreter
{

/**
 * Stores a single position in time and space of single IR blob. This class is
 *	immutable
 * @author EB
 * @version 1.0
 */
class Frame
{

	/**
	 * Be friends with Track so it can set the next frame
	 * @author EB
	 * @version 1.0
	 */
	friend			class Track;

public:
	/**
	 * Create a new immutable frame.
	 * Doesn't store the IR blob id as that would be stored in the Track that
	 *	holds this frame
	 * @param x X co-ordinate of the IR blob
	 * @param y Y co-ordinate of the IR blob
	 * @param size Size of the IR blob
	 * @param time Current time held by the Recorder
	 * @author EB
	 * @version 1.0
	 */
					Frame
					(	int const			x,
						int const			y,
						int const			size,
						uint const			time
					);
	/**
	 * The x co-ordinate of the blob at the recorded time
	 * @return Get the x co-ordinate of the blob
	 * @author EB
	 * @version 1.0
	 */
	int				x						(void)	const;
	/**
	 * The y co-ordinate of the blob at the recorded time
	 * @return Get the y co-ordinate of the blob
	 * @author EB
	 * @version 1.0
	 */
	int				y						(void)	const;
	/**
	 * The x vector amount from the blob at the recorded time to the
	 *	blob at the following time. This will be 0 if there is no next
	 *	frame, or if it's been determined that this and the next blob
	 *	positions are unrelated. i.e. If the parser found that frames
	 *	were dropped or an IR light was off for a period of time
	 * @return Get the x vector from this blob to the next
	 * @author EB
	 * @version 1.0
	 */
	int				u						(void)	const;
	/**
	 * The y vector amount from the blob at the recorded time to the
	 *	blob at the following time. This will be 0 if there is no next
	 *	frame, or if it's been determined that this and the next blob
	 *	positions are unrelated. i.e. If the parser found that frames
	 *	were dropped or an IR light was off for a period of time
	 * @return Get the y vector from this blob to the next
	 * @author EB
	 * @version 1.0
	 */
	int				v						(void)	const;
	/**
	 * The size of the IR blob
	 * @return Get the size of the IR blob
	 * @author EB
	 * @version 1.0
	 */
	uint			size					(void)	const;
	/**
	 * The time this Frame was created counted in milliseconds from the
	 *	beginning of the program
	 * @return Get the time this Frame was created
	 * @author EB
	 * @version 1.0
	 */
	tick			time					(void)	const;
	/**
	 * The next frame on the track. This will be 0 if there are no more frames
	 * @return Get the next frame on the track
	 * @author EB
	 * @version 1.0
	 */
	Frame *			next					(void)	const;

private:
	/**
	 * Add the next frame on the track. This will only be called by Track when
	 *	a new frame is created
	 * @param frame The next frame on the track
	 * @return A reference to this
	 * @author EB
	 * @version 1.0
	 */
	Frame &			operator+=
					(	Frame const * const	frame
					);

private:
	/**
	 * x() field
	 * @author EB
	 * @version 1.0
	 * @see x()
	 */
	int				_x;
	/**
	 * y() field
	 * @author EB
	 * @version 1.0
	 * @see y()
	 */
	int				_y;
	/**
	 * size() field
	 * @author EB
	 * @version 1.0
	 * @see size()
	 */
	uint			_size;
	/**
	 * time() field
	 * @author EB
	 * @version 1.0
	 * @see time()
	 */
	tick			_time;
	/**
	 * next() field
	 * @author EB
	 * @version 1.0
	 * @see next()
	 */
	Frame *			_next;

};

}

#endif
