#ifdef __TEST__
#include "Frame.h"
using std::cout;
using std::endl;

namespace interpreter
{

void Frame::RunTest(void)
{

	Frame * frameA = new Frame(0, 0, 0, 0);
	Frame * frameB = new Frame(7, 7, 7, 7);
	Frame * frameC;
	Frame * frameD;
	Frame * frame;
	bool except = false;

	cout << "Two new frames" << endl;
	cout << frameA << endl;
	cout << frameB << endl;

	cout << "Append frameA to frameB" << endl;
	(*frameA) += frameB;

	cout << "Updated frames" << endl;
	cout << frameA << endl;
	cout << frameB << endl;

	cout << "Store frameA in frameC" << endl;
	frameC = frameA;
	cout << "Erase one frame from C and store new C" << endl;
	frameC = frameC->erase(0);
	cout << "Output A and C" << endl;
	cout << (void*)frameA << endl;
	cout << (void*)frameC << endl;
	cout << "Erase another frame from C and store in C" << endl;
	frameC = frameC->erase(0);
	cout << "Output C" << endl;
	cout << frameC << endl;
	cout << "Erase another frame from C and store in C" << endl;
	frameC = frameC->erase(0);

	frameA = new Frame(1, 1, 1, 0);
	frameB = new Frame(2, 2, 2, 0);
	frameC = new Frame(3, 3, 3, 0);
	frameD = new Frame(4, 4, 4, 0);

	(*frameA) += frameB;
	(*frameC) += frameD;

	cout << "Attach frame groups A(1)->B(2) and C(3)->D(4) on A, so it's A->C->D->B" << endl;
	(*frameA) += frameC;
	cout << "Iterate frames" << endl;
	for(frame = frameA; frame != 0; frame = frame->next())
		cout << frame << endl;

	cout << "Get the total number of frames from the POV of A, B, and C" << endl;
	cout << frameA->length() << ", " << frameB->length() << ", " << frameC->length() << endl;

	cout << "What is the last frame from POV of A, B, and C" << endl;
	cout << frameA->last() << endl << frameB->last() << endl << frameC->last() << endl;

	cout << "Get frame A to erase 2 frames and update so frame A points to the start of the new list" << endl;
	// erase(1) - 1 means frame index, so erases frames 0 and 1
	frameA = frameA->erase(1);
	for(frame = frameA; frame != 0; frame = frame->next())
		cout << frame << endl;

	cout << "Erase all frames" << endl;
	frameA = frameA->erase();
	for(frame = frameA; frame != 0; frame = frame->next())
		cout << frame << endl;

	cout << "Create 3 frames joined together" << endl;
	frameA = new Frame(1, 1, 1, 0);
	frameB = new Frame(2, 2, 2, 0);
	frameC = new Frame(3, 3, 3, 0);
	(*((*frameA) += frameB)) += frameC;
	cout << "Delete the first one" << endl;
	delete frameA;
	cout << "Were all 3 deleted" << endl;

	try { cout << frameC << endl; }
	catch(...)
	{	cout << "All frames were deleted" << endl;
		except = true;
	}
	if(except == false)
		cout << "All frames were NOT deleted!" << endl;

}

}

#endif
