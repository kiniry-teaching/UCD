#include "Frame.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// copy constructor
//
Frame::Frame
(	Frame const * const	frame
) :	_x					(frame->_x),
	_y					(frame->_y),
	_size				(frame->_size),
	_time				(frame->_time)
{	// Get this frame to copy the next frame
	if(frame->_next != 0)
		_next = new Frame(frame->_next);
	else
		_next = 0;
}

///////////////////////////////////////////////////////////////////////////////
// get last frame
//
Frame * Frame::last(void) const
{

	if(this == 0)
		return 0;

	if(_next == 0)
		// last() doesn't modify this object, but the
		//	returned value can be modified outside
		return const_cast<Frame*>(this);

	return _next->last();

}

///////////////////////////////////////////////////////////////////////////////
// get frame count
//
uint Frame::length(void) const
{

	if(this == 0)
		return 0;

	if(_next == 0)
		return 1;

	return _next->length() + 1;

}

///////////////////////////////////////////////////////////////////////////////
// add frames
//
Frame * Frame::operator +=
(	Frame *	frame
){

	if(this == 0)
		return 0;

	if(frame == 0)
		return last();

	// Move current next to the added frame's last next
	frame->last()->_next = _next;
	// Set added frame as new next
	_next = frame;

	return last();

}

///////////////////////////////////////////////////////////////////////////////
// erase
//
Frame * Frame::erase
(	uint const	frameIndex	//= ~0ul
){	Frame *		frameFirst;

	if(this == 0)
		return 0;

	if(frameIndex != 0)
		frameFirst = _next->erase(frameIndex - 1);
	else
		frameFirst = _next;

	// Detach this frame before deleting it so
	//	the dtor doesn't erase the linked frames
	_next = 0;
	delete this;

	return frameFirst;

}

}
