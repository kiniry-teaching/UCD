#ifndef PARSER_H_
#define PARSER_H_

#include "../rai/Recorder/Recorder.h"
#include <string>
#include <iostream>
#include <stdlib.h>
using namespace std;

class Parser
{
public:
	Parser();
	Parser(*Recorder);
	void supply(string in){parser(in, in.size());};
	virtual ~Parser();
private:
	void parser(string,int);
	void provide();
	int array[12];
	int control[4];
};

#endif /*PARSER_H_*/
