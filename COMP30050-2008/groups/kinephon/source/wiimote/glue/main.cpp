//#include <boost/python.hpp>
//#include </usr/include/python2.5/Python.h>
#include <iostream>
#include <string>
#include "Python.h"
using namespace std;

int main(int, char **) {
	Py_Initialize();

	//char* FileName = "/media/data/programming/linux/cpp/workspace/Kinephon/source/wiimote/main.py";
	char* FileName = "code.py";
	PyObject* PyFileObject = PyFile_FromString(FileName, "r");
	if (PyFileObject == NULL) {
		PyErr_Clear();
		return 1;
	}



	PyRun_SimpleFile(PyFile_AsFile(PyFileObject), FileName);




	PyObject * module = PyImport_AddModule("__main__"); 

	assert(module);                                     
	PyObject * dictionary = PyModule_GetDict(module);   
	assert(dictionary);                                 
	
	PyObject * wiimote_address
	= PyDict_GetItemString(dictionary, "wiimote_address");    // borrowed reference
	assert(wiimote_address);
	assert(PyString_Check(wiimote_address));
	char* wiimote_address_string = PyString_AsString(wiimote_address); 

	std::cout << wiimote_address_string << std::endl;

	string string_address(wiimote_address_string); 

	if (string_address != "NOT_FOUND") {
		PyRun_SimpleString("establish_connection(wiimote_address)");
		PyRun_SimpleString("initialise_ir_camera()");

		for (int i=0; i<5000; i++) {
			PyRun_SimpleString("report = receive_report()");

			PyObject * report = PyDict_GetItemString(dictionary, "report");
			assert(report);
			assert(PyList_Check(report));
			int size = PyList_Size(report);
			
			for (int j=0; j < size; j++) {
				PyObject * item = PyList_GetItem(report, j);
				assert(item);
				assert(PyInt_Check(item));
				int item_value = PyInt_AsSsize_t(item);
				cout << item_value;
				if (item_value > 99) {
					cout << " ";
				} else if (item_value < 10) {
					cout << "   ";
				} else {
					cout << "  ";
				}
			}
			cout << "\n";
		}


	} else {
		//try again?
	}
	
	PyRun_SimpleString("close_connection()");
	cout << "transmission complete";

	/*
  	if (wiimote_address != NOT_FOUND):
  	    establish_connection(wiimote_address)
  	    initialise_ir_camera()
  	    receive_data()
  	    close_connection()
  	    print "transmission complete"
  	else:
  	    print "transmission failed: wiimote not found"
	 */


	//PyRun_SimpleString("result = 5 ** 2");
	Py_Finalize();
	cout << "python stopped";
	return 0;
}

