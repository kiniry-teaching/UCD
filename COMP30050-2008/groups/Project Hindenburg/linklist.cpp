#include "linklist.h"

linklist::linklist() {
	p=NULL;
}
float linklist::getY(){
   return p->currY;
}
float linklist::getZ(){
	return p->currZ;
}	
float linklist::getX(){
	return p->currX;
	
	
}

void linklist::append(int num) {
	node *q, *t;

	if (p == NULL) {
		p = new node;
		//p->data = num;
		p->currX = num;
		p->currY = num;
		p->currZ = num;
		p->link = NULL;
	} else {
		q = p;
		while (q->link != NULL)
			q = q->link;

		t = new node;
		//t->data = num;

		t->currX = num;
		t->currY = num;
		t->currZ = num;
		t->link = NULL;
		q->link = t;
	}
}

void linklist::add_as_first(int num) {
	node *q;

	q = new node;
	// q->data = num;
	q->currX = num;
	q->currY = num;
	q->currZ = num;
	q->link = p;
	p = q;
}

void linklist::addafter(int c, int num) {
	node *q, *t;
	int i;
	for (i=0, q=p; i<c; i++) {
		q = q->link;
		if (q == NULL) {
			cout<<"\nThere are less than "<<c<<" elements.";
			return;
		}
	}

	t = new node;
	//t->data = num;
	t->currX = num;
	t->currY = num;
	t->currZ = num;
	t->link = q->link;
	q->link = t;
}

void linklist::del(int num) {
	node *q, *r;
	q = p;
	//q->data == num
	if (q->currX == num && q->currY == num && q->currZ == num) {
		p = q->link;
		delete q;
		return;
	}

	r = q;
	while (q!=NULL) { //q->data == num
		if (q->currX == num && q->currY == num && q->currZ == num) {
			r->link = q->link;
			delete q;
			return;
		}

		r = q;
		q = q->link;
	}
	cout<<"\nElement "<<num<<" not Found.";
}

void linklist::display() {
	node *q;
	cout<<endl;

	for (q = p; q != NULL; q = q->link)
		cout<<endl<<q->currX;
	cout<<endl<<q->currY;
	cout<<endl<<q->currZ;
}

int linklist::count() {
	node *q;
	int c=0;
	for (q=p; q != NULL; q = q->link)
		c++;

	return c;
}

linklist::~linklist() {
	node *q;
	if (p == NULL)
		return;

	while (p != NULL) {
		q = p->link;
		delete p;
		p = q;
	}
}
