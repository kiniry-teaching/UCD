#ifdef WIN32
#	pragma warning(disable: 4786)
#endif
#include "Recorder.h"

using namespace std;

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
	uint const	frameIndex	//= ~0
){	Track *		track		= findTrack(iid);

	if(track == 0)
		return;

	track->erase(frameIndex);

	// If the track is empty and was lost, erase the track
	if(track->hasFrames() == false
	&& track->isLost() == true)
		eraseTrack(iid);

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
(	ect const	control,
	irid const	iid
){

	switch(control)
	{	case econtrol::FOUND:	return controlFound(iid);
		case econtrol::LOST:	return controlLost(iid);
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
	if(track == 0 || track->isLost() == true)
		return;

	frame = new Frame(x, y, size, time);
	(*track) += frame;

}

///////////////////////////////////////////////////////////////////////////////
// find track
//
Track * Recorder::findTrack
(	irid const					iid
){	vector<Track*>::iterator	iTrack;

	for(iTrack = _tracks.begin(); iTrack != _tracks.end(); iTrack++)
		if((*iTrack)->iid() == iid)
			return (*iTrack);

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// find track
//
void Recorder::eraseTrack
(	irid const					iid		//= ~0
){	vector<Track*>::iterator	iTrack;

	if(iid == ~0)
	{
	
		for(iTrack = _tracks.begin(); iTrack != _tracks.end(); iTrack++)
			delete (*iTrack);

		_tracks.erase(_tracks.begin(), _tracks.end());

	}
	else
		for(iTrack = _tracks.begin(); iTrack != _tracks.end(); iTrack++)
			if((*iTrack)->iid() == iid)
			{	delete (*iTrack);
				_tracks.erase(iTrack);
				break;
			}

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
		eraseTrack(iid);
	else
	if(track->isLost() == false)
		track->isLost() = true;

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// control bad communication
//
int Recorder::controlBadcom(void)
{	uint index;

	// Mark all tracks as being up for deletion
	for(index = 0; index < _tracks.size(); index++)
		controlLost(_tracks[index]->iid());

	return 0;

}

}
