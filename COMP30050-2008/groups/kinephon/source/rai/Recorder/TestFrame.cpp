#ifdef __TEST__
#include <cassert>
#include "Frame.h"
#include "../TestMemory.h"
using std::cout;
using std::endl;

namespace interpreter
{

void Frame::RunTest(void)
{

	cout << "Running Frame tests.. ";

	{

	stage++; Frame * frameA = new Frame(1, 2, 3, 4);
	stage++; Frame * frameB = new Frame(5, 6, 7, 8);
	Frame * frameC;
	Frame * frameD;
	Frame * frameCopy;
	bool except = true;

	// Test a frame is created correctly
	assert(frameA->x() == 1);
	assert(frameA->y() == 2);
	assert(frameA->size() == 3);
	assert(frameA->time() == 4);
	assert(frameA->gap() == false);
	assert(frameA->next() == 0);
	assert(frameA->last() == frameA);
	assert(frameA->length() == 1);
	assert(frameA->u() == 0);
	assert(frameA->v() == 0);

	// Join two frames and test they join correctly
	(*frameA) += frameB;
	assert(frameA->gap() == false);
	assert(frameA->next() == frameB);
	assert(frameA->last() == frameB);
	assert(frameA->length() == 2);
	assert(frameB->length() == 1);
	assert(frameA->u() == frameB->x() - frameA->x());
	assert(frameA->v() == frameB->y() - frameA->y());
	assert(frameB->u() == 0);
	assert(frameB->v() == 0);

	// Erase one frame (0 means, erase frame at index 0)
	frameC = frameA;
	frameC = frameC->erase(0);

	assert(frameC == frameB);
	assert(frameC->gap() == false);
	assert(frameC->next() == 0);
	assert(frameC->last() == frameB);
	assert(frameC->length() == 1);
	assert(frameB->length() == 1);
	assert(frameC->u() == 0);
	assert(frameC->v() == 0);
	assert(frameB->u() == 0);
	assert(frameB->v() == 0);

	frameC = frameC->erase(0);
	assert(frameC == 0);

	// Don't crash if erase on a 0 frame
	frameC = frameC->erase(0);
	assert(frameC == 0);

	// Create two groups of frames
	stage++; frameA = new Frame(1, 1, 1, 0);
	stage++; frameB = new Frame(2, 2, 2, 1000);
	stage++; frameC = new Frame(3, 3, 3, 1);
	stage++; frameD = new Frame(4, 4, 4, 0);
	(*frameA) += frameB;
	(*frameC) += frameD;
	assert(frameA->gap() == true);
	assert(frameB->gap() == false);
	assert(frameC->gap() == true);
	assert(frameD->gap() == false);
	assert(frameA->next() == frameB);
	assert(frameB->next() == 0);
	assert(frameC->next() == frameD);
	assert(frameD->next() == 0);
	assert(frameA->length() == 2);
	assert(frameC->length() == 2);

	// Join two groups of frames
	(*frameA) += frameC;
	assert(frameA->next() == frameC);
	assert(frameC->next() == frameD);
	assert(frameD->next() == frameB);
	assert(frameB->next() == 0);
	assert(frameA->length() == 4);
	assert(frameC->length() == 3);
	assert(frameD->length() == 2);
	assert(frameB->length() == 1);
	assert(frameA->last() == frameB);
	assert(frameC->last() == frameB);
	assert(frameD->last() == frameB);
	assert(frameB->last() == frameB);

	// Run copy constructor
	stage++; frameCopy = new Frame(frameA);
	assert(frameCopy->length() == frameA->length());
	assert(frameCopy->x() == frameA->x());
	assert(frameCopy->next()->x() == frameA->next()->x());
	assert(frameCopy->last()->x() == frameA->last()->x());
	assert(frameCopy != frameA);
	assert(frameCopy->next() != frameA->next());
	assert(frameCopy->last() != frameA->last());
	delete frameCopy;

	// Erase 1 frame test links are still correct
	// erase(1) - 1 means frame index, so erases frames 0 and 1
	frameA = frameA->erase(1);
	assert(frameA->next() == frameB);
	assert(frameB->next() == 0);
	assert(frameA->length() == 2);
	assert(frameB->length() == 1);
	assert(frameA->last() == frameB);
	assert(frameB->last() == frameB);

	frameA = frameA->erase();
	assert(frameA == 0);

	// Create 3 frames linked together and delete the first
	//	one - destructor should delete all 3
	stage++; frameA = new Frame(1, 1, 1, 0);
	stage++; frameB = new Frame(2, 2, 2, 0);
	stage++; frameC = new Frame(3, 3, 3, 0);
	stage = -1;
	(*((*frameA) += frameB)) += frameC;
	delete frameA;
#	ifdef WIN32
	// Test all 3 were deleted by accessing the 3rd one, if
	//	it throws an exception, it was deleted OK
	try { cout << frameA << endl; except = false; } catch(...) { }
	try { cout << frameB << endl; except = false; } catch(...) { }
	try { cout << frameC << endl; except = false; } catch(...) { }
	if(except == false)
		assert(false);
#	endif

	cout << "Done" << endl;

	}
	dumpMemoryReport();

}

}

#endif
