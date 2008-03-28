#pragma warning(disable: 4786)
#include <iostream>
using namespace std;
using std::cout;
using std::endl;

int const MS = 3;
int const MM = 100*MS;
extern int stage;
extern int alloc;
extern int mm[MM];

inline void * __cdecl operator new
(	size_t	size
){	void *	m		= malloc(size);
	int		i;
	for(i = 0; i < MM; i += MS)
		if(mm[i] == 0) { mm[i] = (int)m; mm[i+1] = size; mm[i+2] = ::stage; break; }
	if(i == MM)
		assert(false);
	alloc++;
	return m;
}

inline void __cdecl operator delete
(	void *	m
){	int		i;
	alloc--;
	for(i = 0; i < MM; i += MS)
		if(mm[i] == (int)m) { mm[i] = 0; break; }
	if(i == MM)
		assert(false);
	free(m);
}

inline void resetMemoryReport(void)
{	alloc = 0;
}

inline void dumpMemoryReport(void)
{	cout << "Leaks " << alloc << endl;
	for(int i = 0; i < MM; i += MS)
		if(mm[i] != 0) { cout << "Leak at " << mm[i] << ", size " << mm[i+1] << ", stage " << mm[i+2] << endl; }
}