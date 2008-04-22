#ifndef WIIMOTEINTERFACE_H_
#define WIIMOTEINTERFACE_H_
#include <string>
#include "../../Parser/Parser.h"
#include "IRReport.h"
using namespace std;

class WiimoteInterface
{
public:
	WiimoteInterface();
	virtual ~WiimoteInterface();
	
	string findWiimote();
	bool connectTo(string);
	IRReport receiveReport();
	void feedReport(Parser);
	bool closeConnection();
private:
	PyObject * _module;
	PyObject * _dictionary;
	
	
};

#endif /*WIIMOTEINTERFACE_H_*/
