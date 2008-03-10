#include "frame.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// x-vector
//
int Frame::u(void) const
{

	if(_next != 0)
		return _next->x() - _x;

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// y vector
//
int Frame::v(void) const
{

	if(_next != 0)
		return _next->y() - _y;

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// print
//
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
