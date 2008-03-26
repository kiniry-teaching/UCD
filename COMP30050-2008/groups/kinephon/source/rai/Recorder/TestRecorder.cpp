#ifdef __TEST__
#include <cassert>
#include "Recorder.h"
using std::cout;
using std::endl;

namespace interpreter
{

void Recorder::RunTest(void)
{

	cout << "Running Recorder tests" << endl;

	// Test initial state
	Recorder recorder;
	assert(recorder._tracks.size() == 0);

	// Test meaningless changes to empty recorder
	recorder.record(0, 0, 0, 0, 0);
	recorder.control(econtrol::LOST, 0);
	recorder.control(econtrol::BADCOM, 0);
	assert(recorder._tracks.size() == 0);

	// Add a track
	recorder.control(econtrol::FOUND, 5);
	assert(recorder._tracks.size() == 1);

	// Duplicate a track
	recorder.control(econtrol::FOUND, 5);
	assert(recorder._tracks.size() == 1);

	// Add frames to unknown track and added track
	recorder.record(0, 0, 0, 0, 0);
	recorder.record(5, 0, 0, 0, 0);
	assert(recorder._tracks.size() == 1);
	assert(recorder.findTrack(5)->length() == 1);

	// Erase frames from unknown track and added track
	recorder.erase(0, 0);
	recorder.erase(5, 0);
	assert(recorder._tracks.size() == 1);
	assert(recorder.findTrack(5)->hasFrames() == false);

	// Erase again from added track
	recorder.erase(5, 0);
	assert(recorder._tracks.size() == 1);
	assert(recorder.findTrack(5)->hasFrames() == false);

	// Lose the added track
	recorder.control(econtrol::LOST, 5);
	assert(recorder._tracks.size() == 0);

	// Record into the lost track
	recorder.record(5, 0, 0, 0, 0);
	assert(recorder._tracks.size() == 0);

	// Find the track again and add a frame
	recorder.control(econtrol::FOUND, 5);
	recorder.record(5, 0, 0, 0, 0);
	assert(recorder._tracks.size() == 1);
	assert(recorder.findTrack(5)->length() == 1);

	// Lose the track again and erase the frame after losing it
	recorder.control(econtrol::LOST, 5);
	assert(recorder._tracks.size() == 1);
	recorder.erase(5, 0);
	assert(recorder._tracks.size() == 0);

	// Find the track again and add a frame
	recorder.control(econtrol::FOUND, 5);
	recorder.record(5, 0, 0, 0, 0);
	assert(recorder._tracks.size() == 1);
	assert(recorder.findTrack(5)->length() == 1);

	// Lose, then refind the track and then erase the frame
	recorder.control(econtrol::LOST, 5);
	assert(recorder._tracks.size() == 1);
	recorder.control(econtrol::FOUND, 5);
	assert(recorder._tracks.size() == 1);
	recorder.erase(5, 0);
	assert(recorder._tracks.size() == 1);
	assert(recorder.findTrack(5)->hasFrames() == false);

	// Todo

	cout << "Recorder tests complete" << endl;

}

}

#endif
