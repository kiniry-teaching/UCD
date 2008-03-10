#pragma warning(disable: 4786)
#include "Recorder.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// eject
//
Recording * Recorder::eject(void) const
{	Recording * recording;

	recording = new Recording(_tracks);

	return recording;

}

///////////////////////////////////////////////////////////////////////////////
// erase frame
//
void Recorder::erase
(	irid const	iid,
	int const	frameIndex	//= -1
){	Track *		track		= _tracks[iid];
	Frame *		frame		= (*track)[frameIndex];
	Frame *		frameNext	;

	// Note: if the iid is invalid, track will point to 0.
	//	track[frame] will then also return 0 (and not crash,
	//	if that's what you're thinking)

	// Deallocate all removed frames
	while(frame != 0)
	{	frameNext = frame->_next;
		delete frame;
		frame = frameNext;
	}

}

///////////////////////////////////////////////////////////////////////////////
// erase recording
//
void Recorder::erase
(	Recording *	recording
){	delete recording;
}

///////////////////////////////////////////////////////////////////////////////
// control
//
int Recorder::control
(	uchar const control,
	void *		data
){

	switch(control)
	{	case econtrol::FOUND:	return controlFound((int)data);
		case econtrol::LOST:	return controlLost((int)data);
		case econtrol::BADCOM:	return controlBadcom();
	}

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// record
//
void Recorder::record
(	irid const	iid,
	int const	x,
	int const	y,
	int const	size
){

	Track * track = _tracks[iid];

}

///////////////////////////////////////////////////////////////////////////////
// control found
//
int Recorder::controlFound
(	irid	iid
){	Track *	track	= _tracks[iid];

	// New track, allocate and store
	if(track == 0)
	{	track = new Track(iid);
		_tracks[iid] = track;
	}
	else
	// Track has been found before it was deallocated
	if(track->_isLost == true)
		track->_isLost = false;

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// control lost
//
int Recorder::controlLost
(	irid	iid
){	Track *	track	= _tracks[iid];

	// If there are no frames in the track, erase its ass
	//	otherwise, mark it for deletion when all its frames are used
	if(track->_length == 0)
		erase(iid);
	else
	if(track->_isLost == false)
		track->_isLost = true;

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// control bad communication
//
int Recorder::controlBadcom(void)
{

	// Mark all tracks as being up for deletion
	for
	(	std::map<irid, Track *>::iterator i = _tracks.begin();
		i != _tracks.end();
		i++
	)	controlLost(i->first);

	return 0;

}

}
