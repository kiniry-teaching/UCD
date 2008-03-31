#ifndef __INTERPRETER_TESTMEMORY_H__
#define __INTERPRETER_TESTMEMORY_H__

#ifdef __TEST__
#	define __MEMORY__
#endif

#ifdef __MEMORY__

#ifdef WIN32
#	pragma warning(disable: 4786)
#endif
#include <cassert>
#include <iostream>
using namespace std;
using std::cout;
using std::endl;

#ifdef __TEST__
#	ifdef WIN32
		int const MS = 3;
		int const MM = 100*MS;
#	else
#		define MS 3
#		define MM 100*MS
#	endif
	extern int stage;
	extern int mm[MM];
#endif
extern int alloc;

inline void * __cdecl operator new
(	size_t	size
){	void *	m		= malloc(size);
#ifdef __TEST__
	int		i;
	for(i = 0; i < MM; i += MS)
		if(mm[i] == 0) { mm[i] = (int)m; mm[i+1] = size; mm[i+2] = ::stage; break; }
	if(i == MM)
		assert(false);
#endif
	alloc++;
	return m;
}

inline void __cdecl operator delete
(	void *	m
){
	if(m == 0)
		return;
#ifdef __TEST__
	int		i;
	for(i = 0; i < MM; i += MS)
		if(mm[i] == (int)m) { mm[i] = 0; break; }
	if(i == MM)
		assert(false);
#endif
	alloc--;
	free(m);
}

inline void dumpMemoryReport(void)
{
#ifdef __TEST__
	for(int i = 0; i < MM; i += MS)
		if(mm[i] != 0 && mm[i+2] != -1) { cout << "Leak at " << mm[i] << ", size " << mm[i+1] << ", stage " << mm[i+2] << endl; }
#endif
	cout << "Open allocations: " << alloc << endl;
}

#endif

#endif
