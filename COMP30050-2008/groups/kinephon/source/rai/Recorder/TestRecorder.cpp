#ifdef __TEST__
#include <cassert>
#include "Recorder.h"
#include "../TestMemory.h"
using std::cout;
using std::endl;

namespace interpreter
{

void Recorder::RunTest(void)
{

	cout << "Running Recorder/Recording tests.. ";


	bool except = true;

	{

	// Test initial state
	::stage++; Recorder recorder;
	::stage++; assert(recorder._tracks.size() == 0);

	// Test meaningless changes to empty recorder
	::stage++; recorder.record(0, 0, 0, 0, 0);
	::stage++; recorder.control(econtrol::LOST, 0);
	::stage++; recorder.control(econtrol::BADCOM, 0);
	::stage++; assert(recorder._tracks.size() == 0);

	// Add a track
	::stage++; recorder.control(econtrol::FOUND, 5);
	::stage++; assert(recorder._tracks.size() == 1);

	// Duplicate a track
	::stage++; recorder.control(econtrol::FOUND, 5);
	::stage++; assert(recorder._tracks.size() == 1);

	// Add frames to unknown track and added track
	::stage++; recorder.record(0, 0, 0, 0, 0);
	::stage++; recorder.record(5, 0, 0, 0, 0);
	::stage++; assert(recorder._tracks.size() == 1);
	::stage++; assert(recorder.findTrack(5)->length() == 1);

	// Erase frames from unknown track and added track
	::stage++; recorder.erase(0, 0);
	::stage++; recorder.erase(5, 0);
	::stage++; assert(recorder._tracks.size() == 1);
	::stage++; assert(recorder.findTrack(5)->hasFrames() == false);

	// Erase again from added track
	::stage++; recorder.erase(5, 0);
	::stage++; assert(recorder._tracks.size() == 1);
	::stage++; assert(recorder.findTrack(5)->hasFrames() == false);

	// Lose the added track
	::stage++; recorder.control(econtrol::LOST, 5);
	::stage++; assert(recorder._tracks.size() == 0);

	// Record into the lost track
	::stage++; recorder.record(5, 0, 0, 0, 0);
	::stage++; assert(recorder._tracks.size() == 0);

	// Find the track again and add a frame
	::stage++; recorder.control(econtrol::FOUND, 5);
	::stage++; recorder.record(5, 0, 0, 0, 0);
	::stage++; assert(recorder._tracks.size() == 1);
	::stage++; assert(recorder.findTrack(5)->length() == 1);

	// Lose the track again and erase the frame after losing it
	::stage++; recorder.control(econtrol::LOST, 5);
	::stage++; assert(recorder._tracks.size() == 1);
	::stage++; recorder.erase(5, 0);
	::stage++; assert(recorder._tracks.size() == 0);

	// Find the track again and add a frame
	::stage++; recorder.control(econtrol::FOUND, 5);
	::stage++; recorder.record(5, 0, 0, 0, 0);
	::stage++; assert(recorder._tracks.size() == 1);
	::stage++; assert(recorder.findTrack(5)->length() == 1);

	// Lose, then refind the track and then erase the frame
	::stage++; recorder.control(econtrol::LOST, 5);
	::stage++; assert(recorder._tracks.size() == 1);
	::stage++; recorder.control(econtrol::FOUND, 5);
	::stage++; assert(recorder._tracks.size() == 1);
	::stage++; recorder.erase(5, 0);
	::stage++; assert(recorder._tracks.size() == 1);
	::stage++; assert(recorder.findTrack(5)->hasFrames() == false);

	// Add a few frames to test recording
	::stage++; recorder.record(5, 1, 1, 1, 3);
	::stage++; recorder.record(5, 1, 1, 2, 4);
	::stage++; recorder.record(5, 1, 1, 3, 9);
	::stage++; recorder.record(5, 1, 1, 4, 9);
	::stage++; assert(recorder.findTrack(5)->length() == 4);

	::stage++; Recording * recording = recorder.eject();
	::stage++; assert(recording != 0);

	::stage++; assert(recording->length() == recorder._tracks.size());
	::stage++; assert((*recording)[0]->iid() == recorder.findTrack(5)->iid());
	::stage++; assert((*recording)[0]->length() == recorder.findTrack(5)->length());
	::stage++; assert((*recording)[0]->first()->time() == recorder.findTrack(5)->first()->time());
	::stage++; assert((*recording)[0]->first()->time() == recorder.findTrack(5)->first()->time());
	::stage++; recorder.erase(recording);

#	ifdef WIN32
	::stage++;
	try { cout << (*recording)[0]->first() << endl; except = false; } catch(...) { }
	if(except == false)
		assert(false);
#	endif
	::stage = -1;

	cout << "Done" << endl;

	}
	dumpMemoryReport();

}

}

#endif
