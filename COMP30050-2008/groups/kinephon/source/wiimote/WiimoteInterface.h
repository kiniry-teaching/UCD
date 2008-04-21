#ifndef WIIMOTEINTERFACE_H_
#define WIIMOTEINTERFACE_H_
#include <string>
#include "../../Parser/Parser.h"
#include "IRReport.h"
using namespace std;

/**
 * This is the main interface between the wiimote/python
 * and the rest of the system. All of the gluing of python
 * and C++ is done here as well as all the interaction
 * with the python interpreter (including initialisation
 * and exiting of the interpreter).
 * When working with this interface, it is essential that
 * the functions be executed in a very specific order.
 * 1/ findWiimote()
 * only after a valid BT address string is returned can
 * 2/ connectTo() be executed with the address as a parameter
 * this also automaticallly prepares the wiimote for sending
 * data (and makes it start sending it) so that
 * 3/ receiveReport() or feedReport() can be run for
 * as long as necessary to extract data from the wiimote.
 * After we have received all the data we ever wanted the
 * interface has to be closed using the closeConnection()
 * function or by destroying the object.
 * @author JD
 */
class WiimoteInterface
{
public:
	/**
	 * Create a wiimote interface.
	 * Initialises the python interpreter and preloads a script
	 * (from an external file) with all the necessary
	 * functions that will be used from within the python
	 * interpreter.
	 * @author JD
	 */
	WiimoteInterface();
	
	/**
	 * Destroy the interface.
	 * This also closes the python interpreter and closes
	 * the bluetooth connection to the wiimote if it is still
	 * open.
	 * @author JD
	 */
	virtual ~WiimoteInterface();
	
	/**
	 * Finds all bluetooth enabled devices around
	 * and checks if any of them is a wiimote
	 * if it finds one, its bluetooth address will
	 * be returned. If multiple wiimotes are found,
	 * it will return the address of the first one
	 * that is found.
	 * @return a stting containing the bluetooth address
	 * of the first wiimote that was found. If there were
	 * none found, it returns a "NOT_FOUND" string instead.
	 * @author JD
	 */
	string findWiimote();
	
	/**
	 * Connects to a wiimote address specified as a parameter.
	 * TODO	If the connection cannot be established, the
	 * python interpreter will throw and exception which
	 * is not catched and dealt with at the moment.
	 * @return true if the connection was established,
	 * false otherwise
	 * @author JD
	 */
	bool connectTo(string);
	
	/**
	 * Receives a single report from the wiimote,
	 * processes the data (stripping the unnecessary
	 * data in the process) slaps a timestamp to it and
	 * returns it as a IRReport.
	 * @return the report that was received
	 * @author JD
	 */
	IRReport receiveReport();
	
	//TODO finish documentation
	void feedReport(Parser);
	bool closeConnection();
private:
	PyObject * _module;
	PyObject * _dictionary;
	bool active;
};

#endif /*WIIMOTEINTERFACE_H_*/
