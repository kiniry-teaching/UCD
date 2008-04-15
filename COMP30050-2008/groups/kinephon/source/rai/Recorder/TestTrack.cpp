#include <cassert>
#include "Track.h"
#include "../TestMemory.h"
using std::cout;
using std::endl;

#ifdef __TEST__

namespace interpreter
{

void Track::RunTest(void)
{

	cout << "Running Track tests.. ";

	{

	stage++; Track * track = new Track(5);
	Track * trackCopy;
	bool except = true;

	// Initialised correctly
	assert(track->first() == 0);
	assert(track->iid() == 5);
	assert(track->hasFrames() == false);
	assert(track->length() == 0);

	// Adds frames correctly
	stage++; Frame * frameA = (*track) += new Frame(0, 0, 0, 0);
	assert(track->first() == frameA);
	assert(track->iid() == 5);
	assert(track->hasFrames() == true);
	assert(track->length() == 1);

	stage++; Frame * frameB = (*track) += new Frame(1, 1, 1, 1);
	assert(track->first() == frameA);
	assert(track->iid() == 5);
	assert(track->hasFrames() == true);
	assert(track->length() == 2);

	stage++; Frame * frameC = (*track) += new Frame(2, 2, 2, 2);
	assert(track->first() == frameA);
	assert(track->iid() == 5);
	assert(track->hasFrames() == true);
	assert(track->length() == 3);

	// Copy constructor
	stage++; trackCopy = new Track(track);
	assert(trackCopy->length() == track->length());
	assert(trackCopy->first()->x() == track->first()->x());
	assert(trackCopy->hasFrames() == track->hasFrames());
	assert(trackCopy->iid() == track->iid());
	assert(trackCopy->isLost() == track->isLost());
	assert(trackCopy != track);
	assert(trackCopy->first() != track->first());
	delete trackCopy;

	// Erase single frame correctly
	track->erase(0);
	assert(track->first() == frameB);
	assert(track->iid() == 5);
	assert(track->hasFrames() == true);
	assert(track->length() == 2);

	// Erase all frames correctly
	track->erase();
	assert(track->first() == 0);
	assert(track->iid() == 5);
	assert(track->hasFrames() == false);
	assert(track->length() == 0);

	// Were all frames physically deleted,
	//  and not just removed from the track
	try { cout << frameA << endl; except = false; } catch(...) { }
	try { cout << frameB << endl; except = false; } catch(...) { }
	try { cout << frameC << endl; except = false; } catch(...) { }
	if(except == false)
		assert(false);

	assert(track->isLost() == false);
	track->isLost() = true;
	assert(track->isLost() == true);
	track->isLost() = false;
	assert(track->isLost() == false);

	// Frames deleted with track
	stage++; frameA = (*track) += new Frame(0, 0, 0, 0);
	stage = -1;
	delete track;

#	ifdef WIN32
	try { cout << frameA << endl; except = false; } catch(...) { }
	if(except == false)
		assert(false);
#	endif

	cout << "Done" << endl;

	}
	dumpMemoryReport();

}

}

#endif
