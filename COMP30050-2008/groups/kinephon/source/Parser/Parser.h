#ifndef PARSER_H_
#define PARSER_H_

#include "../rai/Recorder/IParserRecorder.h"
#include <string>
#include <iostream>
#include <stdlib.h>
#include <cmath>
using namespace std;
using namespace econtrol;

class Parser
{
public:
	Parser();
	Parser(IParserRecorder* ipr);
	//The format of supply will be changed to accept an array
	void supply(string in){parser(in, in.size());};
	virtual ~Parser();
private:
	void parser(string,int);
	void provide();
	void binary(int);
	int MSB_Extract(int,int);
	int Size_Extract();
	int reportData[12],MSB_Size_Array[8],control[4],binaryPosition,binaryX[8], binaryY[8];
};

#endif /*PARSER_H_*/
