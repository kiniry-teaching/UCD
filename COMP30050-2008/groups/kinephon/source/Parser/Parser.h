#ifndef PARSER_H_
#define PARSER_H_

#include "IParserRecorder.h"
#include <string>
#include <iostream>
#include <stdlib.h>
using namespace std;

class Parser
{
public:
	Parser();
	Parser(IParserRecorder);
	void supply(string in){parser(in, in.size());};
	virtual ~Parser();
private:
	void parser(string,int);
	void provide();
	int x,y,size;
	int array[12];
};

#endif /*PARSER_H_*/
