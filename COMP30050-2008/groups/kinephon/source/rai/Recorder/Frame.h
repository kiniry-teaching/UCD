#ifndef __INTERPRETER_FRAME_H__
#define __INTERPRETER_FRAME_H__

#include <iostream>
#include "../../type.h"
using std::ostream;

namespace interpreter
{

/**
 * Stores a single position in time and space of single IR blob.
 * @author EB
 * @version 1.0
 */
class Frame
{

///////////////////////////////////////////////////////////////////////////////
// friends
//
	/**
	 * Be friends with Recorder so it can create new frames
	 * @author EB
	 * @version 1.0
	 */
	friend		class Recorder;
	/**
	 * Be friends with Recording so it can create new frames
	 * @author EB
	 * @version 1.0
	 */
	friend		class Recording;
	/**
	 * Be friends with Track so it can delete frames
	 * @author EB
	 * @version 1.0
	 */
	friend		class Track;
	/**
	 * Be friends with cout stream writer
	 * @param stream The stream to write to
	 * @param frame This frame to output
	 * @author EB
	 * @version 1.0
	 */
	friend
	ostream &	operator <<
				(	ostream &	stream,
					Frame *		frame
				);

public:
	/**
	 * Execute a number of test cases for this class
	 * @author EB
	 * @version 1.0
	 */
#	if __TEST__
		static void	RunTest			(void);
#	else
		static void	RunTest			(void) { };
#	endif

///////////////////////////////////////////////////////////////////////////////
// queries
//
public:
	/**
	 * The x co-ordinate of the blob at the recorded time
	 * @return Get the x co-ordinate of the blob
	 * @author EB
	 * @version 1.0
	 */
	int			x				(void)	const;
	/**
	 * The y co-ordinate of the blob at the recorded time
	 * @return Get the y co-ordinate of the blob
	 * @author EB
	 * @version 1.0
	 */
	int			y				(void)	const;
	/**
	 * Test if the Frame following this one is disjoint.
	 * This will be true if there is a gap in the recording that couldn't be
	 *	interpolated, either due to the connection packets being lost or
	 *	the ir blob going out of view for longer than allows the path of the
	 *	blob being guessed
	 * @return true if the next Frame is out of order
	 * @post gap() == true ==> (u() == 0 && v() == 0)
	 * @post next() == 0 ==> gap() == false
	 */
	bool		gap				(void)	const;
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
	int			u				(void)	const;
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
	int			v				(void)	const;
	/**
	 * The size of the IR blob
	 * @return Get the size of the IR blob
	 * @author EB
	 * @version 1.0
	 */
	uint		size			(void)	const;
	/**
	 * The time this Frame was created counted in milliseconds from the
	 *	beginning of the program
	 * @return Get the time this Frame was created
	 * @author EB
	 * @version 1.0
	 */
	tick		time			(void)	const;
	/**
	 * The next frame on the track. This will be 0 if there are no more frames
	 * @return Get the next frame on the track
	 * @author EB
	 * @version 1.0
	 */
	Frame *		next			(void)	const;
	/**
	 * The last frame in the list
	 * @return The last frame
	 * @author EB
	 * @version 1.0
	 * @post this != 0 ==> \result->next() == 0;
	 */
	Frame *		last			(void)	const;
	/**
	 * Calculate the number of frames in this track
	 * @return the number of frames in this track
	 * @author EB
	 * @version 1.0
	 */
	uint		length			(void)	const;

///////////////////////////////////////////////////////////////////////////////
// private queries
//
private:
	/**
	 * Constant value that defines the time difference between frames before
	 *	it's considered a gap
	 * @return The maximum time between frames that are considered contiguous
	 * @author EB
	 * @version 1.0
	 */
	tick		timeGap			(void)	const;
///////////////////////////////////////////////////////////////////////////////
// private commands
//
private:
	/**
	 * Attach a list of frames directly following this frame.
	 * If there are frames following this one, they will follow the
	 *	added frames when this returns,
	 *	i.e [a->b] : [a] += [d->e] == [a->d->e->b]
	 * @param frame The frame list to add
	 * @return The last frame added
	 * @author EB
	 * @version 1.0
	 */
	Frame *		operator +=
				(	Frame *		frame
				);

///////////////////////////////////////////////////////////////////////////////
// friend *tor
//
private:
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
				(	int const	x,
					int const	y,
					int const	size,
					uint const	time
				);
	/**
	 * Delete all following frames along with this one
	 * @author EB
	 * @version 1.0
	 */
				~Frame			(void);

///////////////////////////////////////////////////////////////////////////////
// private commands
//
private:
	/**
	 * Erase this and frameIndex frames following it
	 * If frameIndex is not specified, all frames are erased
	 * @param frameIndex The number of frames following to erase too
	 * @return The frame following the last erased one
	 * @author EB
	 * @version 1.0
	 */
	Frame *		erase
				(	uint const	frameIndex	= ~0ul
				);

///////////////////////////////////////////////////////////////////////////////
// fields
//
private:
	/**
	 * x() field
	 * @author EB
	 * @version 1.0
	 * @see x()
	 */
	int			_x;
	/**
	 * y() field
	 * @author EB
	 * @version 1.0
	 * @see y()
	 */
	int			_y;
	/**
	 * size() field
	 * @author EB
	 * @version 1.0
	 * @see size()
	 */
	uint		_size;
	/**
	 * time() field
	 * @author EB
	 * @version 1.0
	 * @see time()
	 */
	tick		_time;
	/**
	 * next() field
	 * @author EB
	 * @version 1.0
	 * @see next()
	 */
	Frame *		_next;

};

///////////////////////////////////////////////////////////////////////////////

inline Frame::Frame
(	int const	x,
	int const	y,
	int const	size,
	uint const	time
) :	_x			(x),
	_y			(y),
	_size		(size),
	_time		(time),
	_next		(0)
{ }

inline Frame::~Frame(void)
{	delete _next;
}

inline int Frame::x(void) const
{	return _x;
}

inline int Frame::y(void) const
{	return _y;
}

inline bool Frame::gap(void) const
{	// If there's a next and the time between
	//	this and the next is significant..
	if(_next != 0 && _next->_time - _time > timeGap())
		// ..There's a gap
		return true;
	// ..Otherwise there's no gap
	return false;
}

inline int Frame::u(void) const
{	// If there's a next and no gap between this and next..
	if(_next != 0 && gap() == false)
		// ..Return the x vector
		return _next->x() - _x;
	// ..Otherwise return 0
	return 0;
}

inline int Frame::v(void) const
{	// If there's a next and no gap between this and next..
	if(_next != 0 && gap() == false)
		// ..Return the y vector
		return _next->y() - _y;
	// ..Otherwise return 0
	return 0;
}

inline uint Frame::size(void) const
{	return _size;
}

inline tick Frame::time(void) const
{	return _time;
}

inline Frame * Frame::next(void) const
{	return _next;
}

inline tick Frame::timeGap(void) const
{	return (tick)50;
}

inline ostream & operator <<
(	ostream &	stream,
	Frame *		frame
){	if(frame == 0)
		return stream;
	return stream
		<< "(" << frame->_x << ", " << frame->_y << ") "
		<< "[" << frame->u() << ", " << frame->v() << "] "
		<< " : " << frame->_size << ", "  << frame->_time;
}

}

#endif
