#include "frame.h"

namespace interpreter
{

int Frame::u(void) const
{

	if(_next != 0)
		return _next->x() - _x;

	return 0;

}



int Frame::v(void) const
{

	if(_next != 0)
		return _next->y() - _y;

	return 0;

}



Frame * Frame::operator +=
(	Frame *	frame
){

	// Remember the next frame pointed to
	Frame * thisNext = _next;
	Frame * thatNext;

	// Set the added frame as the next in the sequence
	_next = frame;

	// Re-attach the original next if there is one
	if(thisNext != 0)
	{

		// Find the last frame in the added link-list
		for
		(	thatNext = frame;
			thatNext->_next != 0;
			thatNext = thatNext->_next
		);

		// Attach the original next frame on to the end of
		//	the new next frame
		thatNext->_next = thisNext;

	}

	return this;

}



ostream & operator <<
(	ostream &	stream,
	Frame *		frame
){

	return stream
		<< "(" << frame->_x << ", " << frame->_y << ") "
		<< "[" << frame->u() << ", " << frame->v() << "] "
		<< " : " << frame->_size << ", "  << frame->_time;

}

}
