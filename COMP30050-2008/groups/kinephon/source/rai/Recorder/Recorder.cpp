#pragma warning(disable: 4786)
#include "Recorder.h"

namespace interpreter
{

///////////////////////////////////////////////////////////////////////////////
// eject
//
Recording * Recorder::eject(void) const
{	//Recording * recording;

//	recording = new Recording(_tracks);

	return 0;//recording;

}

///////////////////////////////////////////////////////////////////////////////
// erase frame
//
void Recorder::erase
(	irid const	iid,
	uint const	frameIndex	//= ~0
){	Track *		track		= findTrack(iid);

	if(track == 0)
		return;

	track->erase(frameIndex);

	if(track->isLost() == true)
		track->isLost() = false;

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
	int const	size,
	tick const	time
){	Track *		track	= findTrack(iid);
	Frame *		frame	;

	// Don't record frames for unknown tracks
	if(track == 0)
		return;

	frame = new Frame(x, y, size, time);
	(*track) += frame;

}

///////////////////////////////////////////////////////////////////////////////
// control found
//
Track * Recorder::findTrack
(	irid const	iid
)	const
{	int			index;

	for(index = 0; index < _tracks.size(); index++)
		if(_tracks[index]->iid() == iid)
			return _tracks[index];

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// control found
//
int Recorder::controlFound
(	irid	iid
){	Track *	track	= findTrack(iid);

	// New track, allocate and store
	if(track == 0)
	{	track = new Track(iid);
		_tracks.push_back(track);
	}
	else
	// Track has been found before it was deallocated
	if(track->isLost() == true)
		track->isLost() = false;

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// control lost
//
int Recorder::controlLost
(	irid	iid
){	Track *	track	= findTrack(iid);

	if(track == 0)
		return 0;

	// If there are no frames in the track, erase its ass
	//	otherwise, mark it for deletion when all its frames are used
	if(track->hasFrames() == false)
		erase(iid);
	else
	if(track->isLost() == false)
		track->isLost() = true;

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// control bad communication
//
int Recorder::controlBadcom(void)
{	int			index;

	// Mark all tracks as being up for deletion
	for(index = 0; index < _tracks.size(); index++)
		controlLost(_tracks[index]->iid());

	return 0;

}

}
