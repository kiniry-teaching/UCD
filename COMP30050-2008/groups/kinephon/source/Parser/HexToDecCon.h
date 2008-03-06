#ifndef HEXTODECCON_H_
#define HEXTODECCON_H_
enum {F = 15, E = 14, D = 13, C = 12, B = 11, A = 10};

#include <string>
#include <iostream>
#include <sstream>
using namespace std;

class HexToDecCon
{
public:
	HexToDecCon();
	float apply(char[]);
	virtual ~HexToDecCon();
private:
	char charAt(char[],int);
	int charConvert(char);
};

#endif /*HEXTODECCON_H_*/
