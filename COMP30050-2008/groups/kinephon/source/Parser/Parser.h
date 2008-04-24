/*
 * Software Engineering Project III
 * David Swords 05477689
 */

#ifndef PARSER_H_
#define PARSER_H_

#include "../rai/Recorder/IParserRecorder.h"
#include "../wiimote/IRReport.h"
#include <string>
#include <vector>
#include <iostream>
#include <stdlib.h>
#include <cmath>
using namespace std;
using namespace interpreter;

class Parser
{
public:
	Parser();
	/*
	 * This constructor accepts a IParserRecorder pointer.
	 * This pointer is used to pass the necessary information
	 * from the wiimote to the analyser.
	 */
	Parser(IParserRecorder* ipr);
	/*
	 * This method does the work.
	 * First we check the vector of decimal values look to
	 * see if any of them are providing no information. It can
	 * then pass this information on to the analyser so it can
	 * see what points are active.
	 * It then works on a set of three values, each one is a report.
	 * The third value of the report has the following structure
	 * 
	 * 		yyxxssss
	 * 
	 * The first two bits of the byte are the most significant bits of the
	 * Y coordinate, the next two are the MSB of the X coordinate. The last
	 * four is the size value of the point. All of these are big endian.
	 * The values extracted are then added to their decimal values and passed
	 * on to the analyser.
	 */
	void supplyReport(IRReport);
private:
	/*
	 * This is the function I use to turn the third byte
	 * into a binary value so I can extract the additional information.
	 * It works by taking in a integer, checking to see if it greater than
	 * or equal to a 2^n value, if it is then an entry is set to one. It
	 * repeats this cycle an subtracts the last 2^n from the current. The
	 * array being used for the values is global.
	 */
	void populate(int);
	/*
	 * This code takes one of the MSB values and converts it into a
	 * decimal value.
	 */
	int MSB_Extract(int,int);
	/*
	 * This is a function that simply takes that last four values in
	 * the binary array and turns that into a decimal number.
	 */
	int Size_Extract();
	/*
	 * Just a global pointer which I will use for the pointer that is passed
	 * in the constructor.
	 */
	IParserRecorder* iprp;
	int reportData[12],MSB_Size_Array[8],control[4],binaryPosition;
};

#endif /*PARSER_H_*/
