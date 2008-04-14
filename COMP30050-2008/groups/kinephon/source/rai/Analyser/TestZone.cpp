#ifdef __TEST__
#include <cassert>
#include "Zone.h"
#include "../TestMemory.h"
using std::cout;
using std::endl;

namespace interpreter
{

#define DP(D) (3.141592653589f * (D)) / 180.0f
void Zone::RunTest(void)
{

	cout << "Running Zone tests.. ";
	{

	const float DTP = 3.141592653589f / 180.0f;
	Zone zone
	(	10, 10,
		7, 10,
		DP(0), DP(70),
		DP(5), DP(20)
	);

	assert(zone.isInside(18, 18, 10) == false);
	assert(zone.isInside(17, 17, 10) == true);
	assert(zone.isInside(11, 10, 1) == true);
	assert(zone.isInside(10.999f, 10, 1) == true);
	assert(zone.isInside(11.001f, 10, 1) == false);

	cout << "Done" << endl;

	}
	dumpMemoryReport();

}

}

#endif
