#include "track.h"

namespace interpreter
{

Frame * Track::operator []
(	uint const	index
)	const
{	Frame *		frame;
	uint		count;

	// Don't bother search if the index is out of range
	if(index >= _length)
		return 0;

	// Count through each frame until the
	//	indexed frame has been reached
	frame = _frameFirst;
	count = 0;
	while(frame != 0 && count < index)
	{	frame = frame->_next;
		count++;
	}

	return frame;

}



Track & Track::operator +=
(	Frame * const frame
){

	// If there are frames already, attach this one to the end
	if(_frameLast != 0)
	{	_frameLast->_next = frame;
		_frameLast = frame;
	}
	else
	// Make this frame the first and last frame
		_frameFirst = _frameLast = frame;

	/// @todo Set the last frame the the last frame in frame and sync length

	// Sync the length of the track
	_length++;

	return (*this);

}

Track & Track::operator -=
(	Frame * const	frame
){	Frame *			frameLast	= _frameFirst;

	// Find the frame just before the frame to be deleted
	while(frameLast != 0 && frameLast->_next != frame)
		frameLast = frameLast->_next;

	// If the frame being deleted actually exists in this Track
	if(frameLast != 0)
	{

		/// @todo Deallocate all following frames and sync length

		// Make the 
		_frameLast = frameLast;

	}

	return (*this);

}

}
