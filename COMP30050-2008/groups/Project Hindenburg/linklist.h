#ifndef LINKLIST_H_
#define LINKLIST_H_

#include <iostream>

using namespace std;

class linklist {
private:

	struct node {
		// int data;
		float currX, currY, currZ;
		node *link;
	}*p;

public:

	linklist();
	void append(int num);
	void add_as_first(int num);
	void addafter(int c, int num);
	float getX();
	float getY();
	float getZ();
	void del(int num);
	void display();
	int count();
	~linklist();
};
#endif /*LINKLIST_H_*/
