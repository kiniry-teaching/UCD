#ifndef WIIMOTEINTERFACE_H_
#define WIIMOTEINTERFACE_H_
#include <string>
#include "IRReport.h"
using namespace std;

class WiimoteInterface
{
public:
	WiimoteInterface(/*Parser*/);
	virtual ~WiimoteInterface();
	
	string findWiimote();
	bool connectTo(string);
	IRReport receiveData();
	bool closeConnection();
private:
	PyObject * _module;
	PyObject * _dictionary;
	
	
};

#endif /*WIIMOTEINTERFACE_H_*/
