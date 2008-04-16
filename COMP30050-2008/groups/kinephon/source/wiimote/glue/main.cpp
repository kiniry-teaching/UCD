//#include <boost/python.hpp>
//#include </usr/include/python2.5/Python.h>
#include <iostream>
#include "Python.h"

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



  /*
	if (wiimote_address != NOT_FOUND):
	    print wiimote_address
	    establish_connection(wiimote_address)
	    initialise_ir_camera()
	    receive_data()
	    close_connection()
	    print "transmission complete"
	else:
	    print "transmission failed: wiimote not found"
    */
  
  PyObject * module = PyImport_AddModule("__main__"); 
  assert(module);                                     
  PyObject * dictionary = PyModule_GetDict(module);   
  assert(dictionary);                                 
  
  
  PyObject * wiimote_address
  	= PyDict_GetItemString(dictionary, "wiimote_address");    
  assert(wiimote_address);
  assert(PyString_Check(wiimote_address));
  char* wiimote_address_string = PyString_AsString(wiimote_address); 
  
  std::cout << wiimote_address_string << std::endl;
  
  Py_Finalize();
  return 0;
}

