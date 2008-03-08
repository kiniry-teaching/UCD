#pragma warning(disable: 4786)
#include "Recorder.h"

namespace interpreter
{

Recording * Recorder::eject(void) const
{

	return 0;

}



void Recorder::erase
(	irid const	iid,
	int const	frame	//= -1
){

	

}



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



void Recorder::record
(	irid const	iid,
	int const	x,
	int const	y,
	int const	size
){

	Track * track = _tracks[iid];

}



int Recorder::controlFound
(	irid	iid
){	Track *	track	= _tracks[iid];

	if(track == 0)
	{

		track = new Track(iid);
		_tracks[iid] = track;

	}
	else
	// Track has been found before it was deallocated
	if(track->_isLost == true)
		track->_isLost = false;

	return 0;

}



int Recorder::controlLost
(	irid	iid
){	Track *	track	= _tracks[iid];

	// If there are no frames in the track, erase it's ass
	//	otherwise, mark it for deletion when all its frames are used
	if(track->_length == 0)
		erase(iid);
	else
	if(track->_isLost == false)
		track->_isLost = true;

	return 0;

}



int Recorder::controlBadcom(void)
{

	for
	(	std::map<irid, Track *>::iterator i = _tracks.begin();
		i != _tracks.end();
		i++
	)	controlLost(i->first);

	return 0;

}

}
