#ifndef __INTERPRETER_TRACK_H__
#define __INTERPRETER_TRACK_H__

#include "../TestMemory.h"
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
	/**
	 * Be friends with Recording so it can add frames
	 * @author EB
	 * @version 1.0
	 */
	friend		class Recording;

#if __TEST__
///////////////////////////////////////////////////////////////////////////////
// tests
//
public:
	/**
	 * Execute a number of test cases for this class
	 * @author EB
	 * @version 1.0
	 */
	static void	RunTest					(void);
#endif

///////////////////////////////////////////////////////////////////////////////
// queries
//
public:
	/**
	 * Get the IR blob's id being tracked by this
	 * @return The IR blob's id
	 */
	irid		iid						(void)		const;
	/**
	 * Returns the first frame in this Track.
	 * Following frames can be accessed by this->frame()->next()..
	 * @return The first frame in this Track
	 * @author EB
	 * @version 1.0
	 */
	Frame *		first					(void)		const;
	/**
	 * Returns the last frame in this Track.
	 * Previous frames can be accessed by this->frame()->prev()..
	 * @return The last frame in this Track
	 * @author EB
	 * @version 1.0
	 */
	Frame *		last					(void)		const;
	/**
	 * Returns true if there are Frames in the track, else false
	 * @return true if there are Frames in the track, else false
	 * @author EB
	 * @version 1.0
	 */
	bool		hasFrames				(void)		const;
	/**
	 * Calculate the number of frames in this track
	 * @return the number of frames in this track
	 * @author EB
	 * @version 1.0
	 */
	uint		length					(void)		const;

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
				(	irid const			iid
				);
	/**
	 * Copy constructor
	 * Copy all properties and frames (don't copy pointer to frames) make
	 *	complete new copy of all frames
	 * @param track The track to copy
	 * @author EB
	 * @version 1.0
	 */
				Track
				(	Track const * const	track
				);
	/**
	 * Destory all frames in this track
	 * @author EB
	 * @version 1.0
	 */
				~Track					(void);

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
				(	Frame * const		frame
				);
	/**
	 * Erase all frames up to and including frameIndex
	 * If frameIndex is not specified, all frames are erased
	 * @param frameIndex Erase from first frame to frameIndex
	 * @author EB
	 * @version 1.0
	 */
	void		erase
				(	uint const			frameIndex	= ~0ul
				);
	/**
	 * Store whether this track has been lost, is no longer in use. A track
	 *	that is no longer is use can be deleted when all its frames are used
	 * @author EB
	 * @version 1.0
	 */
	bool &		isLost					(void);

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
	_frameFirst		(0),
	_frameLast		(0),
	_isLost			(false)
{ }

inline Track::~Track(void)
{	delete _frameFirst;//erase();
}

inline irid Track::iid(void) const
{	return _iid;
}

inline bool Track::hasFrames(void) const
{	return _frameFirst != 0;
}

inline uint Track::length(void) const
{	return _frameFirst->length();
}

inline Frame * Track::first(void) const
{	return _frameFirst;
}

inline Frame * Track::last(void) const
{	return _frameFirst->last();
}

inline bool & Track::isLost(void)
{	return _isLost;
}

}

#endif
