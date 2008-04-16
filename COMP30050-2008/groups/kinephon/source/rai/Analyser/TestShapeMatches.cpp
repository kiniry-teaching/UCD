#ifdef __TEST__
#include <cassert>
#include "ShapeMatch.h"
#include "ShapeMatches.h"
#include "../TestMemory.h"
using std::cout;
using std::endl;

namespace interpreter
{

void ShapeMatches::RunTest(void)
{

	cout << "Running ShapeMatches/ShapeMatch tests.. ";

	bool except = true;
	{

	::stage++; ShapeMatches shapeMatches(0.75f, 5);
	::stage++; ShapeMatches shapeMatches2(0.80f);
	::stage++; ShapeMatch shapeMatch1(0, 0.72f);
	::stage++; ShapeMatch shapeMatch2(0, 0.76f);
	::stage++; ShapeMatch shapeMatch3(0, 0.80f);
	::stage++; ShapeMatch shapeMatch4(0, 0.90f);
	::stage++; ShapeMatch shapeMatch5(0, 0.79f);
	::stage++; ShapeMatch shapeMatch6(0, 0.81f);
	::stage++; ShapeMatch shapeMatch7(0, 0.96f);
	::stage++; ShapeMatch shapeMatch8(0, 0.73f);
	::stage++; ShapeMatch shapeMatch9(0, 0.99f);
	::stage++; ShapeMatch shapeMatchA(0, 0.80f);

	shapeMatches += &shapeMatch1;
	assert(shapeMatches.length() == 0);
	shapeMatches += &shapeMatch2;
	assert(shapeMatches.length() == 1);
	assert(shapeMatches[0] == &shapeMatch2);
	shapeMatches += &shapeMatch3;
	assert(shapeMatches.length() == 2);
	assert(shapeMatches[0] == &shapeMatch3);
	assert(shapeMatches[1] == &shapeMatch2);
	shapeMatches += &shapeMatch4;
	assert(shapeMatches.length() == 3);
	assert(shapeMatches[0] == &shapeMatch4);
	assert(shapeMatches[1] == &shapeMatch3);
	assert(shapeMatches[2] == &shapeMatch2);
	shapeMatches += &shapeMatch5;
	assert(shapeMatches.length() == 4);
	assert(shapeMatches[0] == &shapeMatch4);
	assert(shapeMatches[1] == &shapeMatch3);
	assert(shapeMatches[2] == &shapeMatch5);
	assert(shapeMatches[3] == &shapeMatch2);
	shapeMatches += &shapeMatch6;
	assert(shapeMatches.length() == 5);
	assert(shapeMatches[0] == &shapeMatch4);
	assert(shapeMatches[1] == &shapeMatch6);
	assert(shapeMatches[2] == &shapeMatch3);
	assert(shapeMatches[3] == &shapeMatch5);
	assert(shapeMatches[4] == &shapeMatch2);
	shapeMatches += &shapeMatch7;
	assert(shapeMatches.length() == 5);
	assert(shapeMatches[0] == &shapeMatch7);
	assert(shapeMatches[1] == &shapeMatch4);
	assert(shapeMatches[2] == &shapeMatch6);
	assert(shapeMatches[3] == &shapeMatch3);
	assert(shapeMatches[4] == &shapeMatch5);
	shapeMatches += &shapeMatch8;
	assert(shapeMatches.length() == 5);
	assert(shapeMatches[0] == &shapeMatch7);
	assert(shapeMatches[1] == &shapeMatch4);
	assert(shapeMatches[2] == &shapeMatch6);
	assert(shapeMatches[3] == &shapeMatch3);
	assert(shapeMatches[4] == &shapeMatch5);
	shapeMatches += &shapeMatch9;
	assert(shapeMatches.length() == 5);
	assert(shapeMatches[0] == &shapeMatch9);
	assert(shapeMatches[1] == &shapeMatch7);
	assert(shapeMatches[2] == &shapeMatch4);
	assert(shapeMatches[3] == &shapeMatch6);
	assert(shapeMatches[4] == &shapeMatch3);
	shapeMatches += &shapeMatchA;
	assert(shapeMatches.length() == 5);
	assert(shapeMatches[0] == &shapeMatch9);
	assert(shapeMatches[1] == &shapeMatch7);
	assert(shapeMatches[2] == &shapeMatch4);
	assert(shapeMatches[3] == &shapeMatch6);
	assert(shapeMatches[4] == &shapeMatch3);

	shapeMatches2 += &shapeMatch6;
	assert(shapeMatches2.length() == 1);
	assert(shapeMatches2[0] == &shapeMatch6);
	shapeMatches2 += &shapeMatch3;
	assert(shapeMatches2.length() == 1);
	assert(shapeMatches2[0] == &shapeMatch6);
	shapeMatches2 += &shapeMatch4;
	assert(shapeMatches2.length() == 1);
	assert(shapeMatches2[0] == &shapeMatch4);
	shapeMatches2 += &shapeMatch6;
	assert(shapeMatches2.length() == 1);
	assert(shapeMatches2[0] == &shapeMatch4);

	::stage = -1;

	cout << "Done" << endl;

	}
	dumpMemoryReport();

}

}

#endif
