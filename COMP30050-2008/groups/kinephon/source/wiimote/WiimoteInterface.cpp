#include <vector>
#include <sys/time.h>
#include <string>
#include "Python.h"
#include "../Parser/Parser.h"
#include "WiimoteInterface.h"
using namespace std;

WiimoteInterface::WiimoteInterface()
{
	active = false;
	Py_Initialize();

	char* FileName = "python_interface.py";
	PyObject* PyFileObject = PyFile_FromString(FileName, "r");
	if (PyFileObject == NULL) {
		//TODO we have a problem
		PyErr_Clear();
	}

	PyRun_SimpleFile(PyFile_AsFile(PyFileObject), FileName);

	_module = PyImport_AddModule("__main__"); 
	assert(_module);                                   
	_dictionary = PyModule_GetDict(_module);   
	assert(_dictionary);    
}

WiimoteInterface::~WiimoteInterface()
{
	//Close the connection if it hasn't been closed already.
	if (active) {
		closeConnection();
	}
	//close the interpreter
	Py_Finalize();
}

string WiimoteInterface::findWiimote()
{
	PyRun_SimpleString("wiimote_address = find_wiimote()");

	PyObject * wiimote_address = PyDict_GetItemString(_dictionary, "wiimote_address");    // borrowed reference
	assert(wiimote_address);
	assert(PyString_Check(wiimote_address));
	char* wiimote_address_string = PyString_AsString(wiimote_address);
	string string_address(wiimote_address_string);

	//	this is just for testing purposes as it takes
	//	about 15 seconds to lookup all the BT enabled
	//	devices around so I can skip this by
	//	hardcoding the BT address of my wiimote
	
	//	string string_address = "00:1E:35:06:74:BD";

	return string_address;
}

bool WiimoteInterface::connectTo(string bluetooth_address) {
	if (bluetooth_address != "NOT_FOUND") {
		//TODO check for exceptions
		PyRun_SimpleString("establish_connection(wiimote_address)");
		PyRun_SimpleString("initialise_ir_camera()");
		active = true;
		return true;
	} else {
		active = false;
		return false;
	}

}

IRReport WiimoteInterface::receiveReport() {
	if (active) {
		PyRun_SimpleString("report = receive_report()");

		PyObject * report = PyDict_GetItemString(_dictionary, "report");
		assert(report);
		assert(PyList_Check(report));
		int size = PyList_Size(report);

		vector<int> data;
		struct timeval time;
		gettimeofday(&time, NULL);
		int timestamp = time.tv_sec *1000 + time.tv_usec /1000;		//this will give us millisecs (*NIX dependent)

		for (int j=0; j < size; j++) {
			PyObject * item = PyList_GetItem(report, j);
			assert(item);
			assert(PyInt_Check(item));
			int item_value = PyInt_AsSsize_t(item);
			if (0 <= item_value && item_value <= 255) {
				data.push_back(item_value);
			} else {
				//TODO what to do when we are getting wrong data?
				//well, we will have an invalid report then...
				//and when it is invalid, it should be dropped before processing.
			}
		}

		IRReport report_object(data, timestamp);
		return report_object;
	} else {
//		return NULL;
	}
}

void WiimoteInterface::feedReport(Parser p) 
{
	if (active) {
		//TODO feed the parser
	} else {
		//do nothing
	}
}

bool WiimoteInterface::closeConnection() {
	PyRun_SimpleString("close_connection()");
	active = false;
}
