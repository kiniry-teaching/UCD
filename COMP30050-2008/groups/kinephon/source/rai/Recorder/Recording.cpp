#include "Recording.h"
using namespace std;

namespace interpreter
{

Recording::Recording
(	vector<Track*> const &			tracks
){	vector<Track*>::const_iterator	iTrack;

	for(iTrack = tracks.begin(); iTrack != tracks.end(); iTrack++)
		_tracks.push_back(new Track(*iTrack));

}

Recording::~Recording(void)
{	vector<Track*>::const_iterator	iTrack;

	for(iTrack = _tracks.begin(); iTrack != _tracks.end(); iTrack++)
		delete (*iTrack);

}

}
