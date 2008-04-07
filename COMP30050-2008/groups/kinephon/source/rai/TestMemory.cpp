#ifdef __TEST__
#	define __MEMORY__
#endif

#ifdef __MEMORY__

#include <cassert>
#include "TestMemory.h"

#ifdef __TEST__
	int stage = -1;
	int mm[MM] = {0};
#endif
int alloc = 0;

#endif
