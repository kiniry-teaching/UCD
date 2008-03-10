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

///////////////////////////////////////////////////////////////////////////////
// friends
//
	/**
	 * Be friends with Recorder so it can add frames
	 * @author EB
	 * @version 1.0
	 */
	friend		class Recorder;

///////////////////////////////////////////////////////////////////////////////
// queries
//
public:
	/**
	 * Get the IR blob's id being tracked by this
	 * @return The IR blob's id
	 */
	irid		iid					(void)	const;
	/**
	 * Returns the first frame in this Track.
	 * Following frams can be accessed by this->frame()->next()..
	 * @return The first frame in this Track
	 * @author EB
	 * @version 1.0
	 */
	Frame *		first				(void)	const;
	/**
	 * Returns the number of frames.
	 * @return The number of frames held by this track
	 * @author EB
	 * @version 1.0
	 */
	uint		length				(void)	const;

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
				(	uint const		index
				)	const;

///////////////////////////////////////////////////////////////////////////////
// friend *tor
//
private:
	/**
	 * Create a new track for a specific IR blob
	 * @param iid The IR blob id that this Track will hold
	 * @author EB
	 * @version 1.0
	 */
				Track
				(	irid const		iid
				);

///////////////////////////////////////////////////////////////////////////////
// friend commands
//
private:
	/**
	 * Add the next frame on the track. This will only be called by Recorder 
	 *	when a new frame needs to be created. This does not allocated new
	 *	frames
	 * @param frame The next frame on the track
	 * @return A reference to this
	 * @author EB
	 * @version 1.0
	 */
	Frame *		operator +=
				(	Frame * const	frame
				);
	/**
	 * Remove a frame and all before.
	 * @param frame The frame to remove from the track
	 * @return A reference to this
	 * @author EB
	 * @version 1.0
	 * @pre frame must exist in the track
	 * @warning This does not deallocate frames
	 * @warning If the specified frame does not exist, all frames are removed
	 */
	Frame *		operator -=
				(	Frame * const	frame
				);
	/**
	 * Store whether this track has been lost, is no longer in use. A track
	 *	that is no longer is use can be deleted when all its frames are used
	 * @author EB
	 * @version 1.0
	 */
	bool		isLost				(void)	const;

///////////////////////////////////////////////////////////////////////////////
// fields
//
private:
	/**
	 * iid()'s field
	 * @author EB
	 * @version 1.0
	 * @see id()
	 */
	irid		_iid;
	/**
	 * length()'s field
	 * @author EB
	 * @version 1.0
	 * @see length()
	 */
	uint		_length;
	/**
	 * first()'s field
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
	/**
	 * lost()'s field
	 * @author EB
	 * @version 1.0
	 * @see lost()
	 */
	bool		_isLost;

};

///////////////////////////////////////////////////////////////////////////////

inline Track::Track
(	irid const		iid
) :	_iid			(iid),
	_length			(0),
	_frameFirst		(0),
	_frameLast		(0),
	_isLost			(false)
{ }

inline irid Track::iid(void) const
{	return _iid;
}

inline uint Track::length(void) const
{	return _length;
}

inline Frame * Track::first(void) const
{	return _frameFirst;
}

inline bool Track::isLost(void) const
{	return _isLost;
}

}

#endif
