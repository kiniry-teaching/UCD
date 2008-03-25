#ifdef __TEST__
#include "Track.h"
using std::cout;
using std::endl;

namespace interpreter
{

void Track::RunTest(void)
{

	Track * track = new Track(5);
	bool except = false;

	cout << "New track's public details" << endl;
	cout << "First frame: " << track->first() << endl;
	cout << "IRID: " << track->iid() << endl;
	cout << "HasFrames: " << track->hasFrames() << endl;
	cout << "Length: " << track->length() << endl;

	cout << "Add a 3 frames and get details" << endl;

	(*track) += new Frame(0, 0, 0, 0);
	(*track) += new Frame(1, 1, 1, 1);
	Frame * frame = (*track) += new Frame(2, 2, 2, 2);

	cout << "First frame: " << track->first() << endl;
	cout << "IRID: " << track->iid() << endl;
	cout << "HasFrames: " << track->hasFrames() << endl;
	cout << "Length: " << track->length() << endl;

	cout << "Erase 1 frame, output" << endl;
	track->erase(0);
	cout << "First frame: " << track->first() << endl;
	cout << "IRID: " << track->iid() << endl;
	cout << "HasFrames: " << track->hasFrames() << endl;
	cout << "Length: " << track->length() << endl;

	cout << "Erase all frames, were all contained frames deleted" << endl;
	track->erase();
	cout << "First frame: " << track->first() << endl;
	cout << "IRID: " << track->iid() << endl;
	cout << "HasFrames: " << track->hasFrames() << endl;
	cout << "Length: " << track->length() << endl;

//	try { cout << frame << endl; }
//	catch(void*)
//	{	cout << "All frames were deleted" << endl;
//		except = true;
//	}
//	if(except == false)
//		cout << "All frames were not deleted!" << endl;

	cout << "Test private lostness" << endl;
	cout << "IsLost: " << track->isLost() << endl;
	track->isLost() = true;
	cout << "IsLost: " << track->isLost() << endl;
	track->isLost() = false;
	cout << "IsLost: " << track->isLost() << endl;

}

}

#endif