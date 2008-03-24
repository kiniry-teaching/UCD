#include "track.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// add frame(s)
//
Frame * Track::operator +=
(	Frame * const frame
){

	// Don't add to an unexsting track
	if(this == 0)
		return frame;

	// If there are frames already, attach this one to the end
	if(_frameLast != 0)
		_frameLast = (*_frameLast) += frame;
	else
	// Make this frame the first and last frame
		_frameFirst = _frameLast = frame;

	return frame;

}

///////////////////////////////////////////////////////////////////////////////
// remove frame(s)
//
void Track::erase
(	uint const	frameIndex //= 0ul
){

	// Don't remove from an unexsting track
	if(this == 0)
		return;

	// Get the frame to erase itself and return
	//	the new first frame
	_frameFirst = _frameFirst->erase(frameIndex);

	// If all the frames were erased, unset the
	//	last frame
	if(_frameFirst == 0)
		_frameLast = 0;

}

}
