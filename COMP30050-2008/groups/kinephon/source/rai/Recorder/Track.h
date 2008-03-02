#ifndef __INTERPRETER_TRACK_H__
#define __INTERPRETER_TRACK_H__

#include "../../type.h"
#include "Frame.h"

namespace interpreter
{

/**
 * Stores all frames for a single IR blob
 * @author EB
 * @version 1.0
 */
class Track
{

	/**
	 * Be friends with Recorder so it can add frames
	 * @author EB
	 * @version 1.0
	 */
	friend		class Recorder;

public:
	/**
	 * Create a new track for a specific IR blob
	 * @param irid The IR blob id that this Track will hold
	 * @author EB
	 * @version 1.0
	 */
				Track
				(	irid const	irid
				);
	/**
	 * Destory this track
	 * @author EB
	 * @version 1.0
	 * @warning Destructor is not virtual, don't inherit from this class
	 */
				~Track			(void);
	/**
	 * Get the IR blob's id being tracked by this
	 * @return The IR blob's id
	 */
	irid		id				(void)	const;
	/**
	 * Returns the number of frames.
	 * @return The number of frames held by this track
	 * @author EB
	 * @version 1.0
	 */
	uint		length			(void)	const;
	/**
	 * Returns the first frame in this Track.
	 * Following frams can be accessed by this->frame()->next()..
	 * @return The first frame in this Track
	 * @author EB
	 * @version 1.0
	 */
	Frame *		first			(void)	const;

	/**
	 * Returns the indexed Frame.
	 * Index should be in the range (0..length()-1)
	 * @param index Index of frame to return, from 0 to length() - 1
	 * @return Indexed frame. If Index is out of range, 0 is returned
	 * @warning It is slower to access each frame by index than sequentially
	 *	from first() and Frame::next() as each indexed frame needs to first
	 *	find the frame.
	 * @author EB
	 * @version 1.0
	 * @pre index >= 0 && index < length();
	 * @post /result != 0;
	 */
	Frame *		operator []
				(	uint const	index
				)	const;

private:
	/**
	 * Add the next frame on the track. This will only be called by Recorder when
	 *	a new frame needs to be created
	 * @param frame The next frame on the track
	 * @return A reference to this
	 * @author EB
	 * @version 1.0
	 */
	Track &		operator+=
				(	Frame const * const	frame
				);

private:
	/**
	 * irid() field
	 * @author EB
	 * @version 1.0
	 * @see id()
	 */
	irid		_irid;
	/**
	 * length() field
	 * @author EB
	 * @version 1.0
	 * @see length()
	 */
	uint		_length;
	/**
	 * first() field
	 * @author EB
	 * @version 1.0
	 * @see first()
	 */
	Frame *		_frameFirst;
	/**
	 * Store a pointer to the last frame to allow quick access when adding a
	 *	new frame
	 * @author EB
	 * @version 1.0
	 */
	Frame *		_frameLast;

};

}

#endif
