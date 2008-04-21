#ifndef PARSER_H_
#define PARSER_H_

//#include "../rai/Recorder/IParserRecorder.h"
#include <string>
#include <iostream>
#include <stdlib.h>
#include <cmath>
using namespace std;

class Parser
{
public:
	Parser();
//	Parser(IParserRecorder* ipr);
	void supply(string in){parser(in, in.size());};
	int getX(){return x;};
	int getY(){return y;};
	virtual ~Parser();
private:
	void parser(string,int);
	void provide();
	void binary(int);
	int MSB_Extract(int,int);
	void invertBinaryValues(int,int);
	int Size_Extract();
	void setX(int in){x=in;};
	void setY(int in){y=in;};
	int reportData[12], MSB_Size_Array[8], control[4], binaryPosition, x, y, binaryX[8], binaryY[8];
};

#endif /*PARSER_H_*/
