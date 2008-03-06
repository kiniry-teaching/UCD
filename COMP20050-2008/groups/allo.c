#define ALLOCSIZE 10000 /*space available*/

static char allocbuf[ALLOCSIZE];  /*storage for alloc*/
static char *allocp = allocbuf;	  /*next free position*/

char *alloc(int n)	/*return pointer to characters*/
{
	if(allocbuf + ALLOCSIZE - allocp >= n) /*it fits*/
		{
		allocp +=n;
		return allocp - n; /* old p*/
		}
	else		/*not enough room*/
		{
		return 0;
		}
}

void afree(char *p)	/*free storage*/
{
	if(p>=allocbuf && p < allocbuf + ALLOCSIZE)
		{
		allocp = p;
		}
}

#include <stdio.h>

main()
{
printf("hello\n");
}
