#ifndef PARSER_H_
#define PARSER_H_

//#include "IParserRecorder.h"
#include <string>
#include <iostream>
#include <stdlib.h>
#include <cmath>
using namespace std;

class Parser
{
public:
	Parser();
//	Parser(IParserRecorder);
	void supply(string in){parser(in, in.size());};
	virtual ~Parser();
private:
	void parser(string,int);
	void provide();
	void binary(int);
	int MSB_Extract(int,int);
	int Size_Extract();
	int reportData[12];
	int MSB_Size_Array[8];
	int control[4];
	int binaryPosition;
};

#endif /*PARSER_H_*/
