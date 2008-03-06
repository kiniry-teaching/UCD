#ifndef PARSER_H_
#define PARSER_H_

/*
 * Author David Swords
 * 05477689
 * Parser acts as a bridge between the Jakub's wiimote communication code and the Recorder/Analyser/Interpreter
 */
 
 #include "source/rai/recorder/IParserRecorder.h"
 
 using namespace std;
 
 class Parser
 {
 	public:
 		Parser();
 		Parser(IParserRecorder);
 		~Parser();
 	private:	
 }