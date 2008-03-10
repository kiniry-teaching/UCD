#include "track.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// track indexer
//
Frame * Track::operator []
(	uint const	index
)	const
{	Frame *		frame;
	uint		count;

	// Don't bother search if the index is out of range
	//	Or this track doesn't exist
	if(this == 0 || index >= _length)
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
	{	_frameLast->_next = frame;
		_frameLast = frame;
	}
	else
	// Make this frame the first and last frame
		_frameFirst = _frameLast = frame;

	// Sync the length of the track
	_length++;

	// If the added frame contained more than one
	//	frame, add all the following ones
	while(_frameLast->_next != 0)
	{	_frameLast = _frameLast->_next;
		_length++;
	}

	return frame;

}

///////////////////////////////////////////////////////////////////////////////
// remove frame(s)
//
Frame * Track::operator -=
(	Frame * const	frame
){	Frame *			frameFirst;
	Frame *			frameFirstDelete;

	// Don't remove from an unexsting track
	//	and return 0 so attempt to deallocate frames is made
	if(this == 0)
		return 0;

	// Logically delete all frames from the original first,
	//	up to and including, the specified frame
	frameFirstDelete = frameFirst = _frameFirst;
	while(frameFirst != 0 && frameFirst != frame)
	{	frameFirst = frameFirst->_next;
		_length--;
	}

	// If there are still frames not removed..
	if(frameFirst != 0)
		// Make the track point at the new first frame
		_frameFirst = frameFirst->_next;
	else
		// else, make the track point at nothing for first and last frames
		_frameFirst = _frameLast = 0;

	// Remove the connection between the removed frame and the frames in
	//	the track and then return the first frame removed. The called can
	//	then iterate from the firstFrameDelete until frame with no next
	//	to deallocate the removed frames
	frame->_next = 0;

	return frameFirstDelete;

}

}
