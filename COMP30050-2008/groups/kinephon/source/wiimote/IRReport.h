#ifndef IRREPORT_H_
#define IRREPORT_H_
#include <vector>
using namespace std;

/**
 * A simple Report object that contains a 12 byte vector with
 * the data from the wiimote and an integet timestamp.
 * @author JD
 */
class IRReport
{
public:
	/**
	 * Created a report.
	 * @param values a vector of ints containing the 12
	 * bytes worth of information
	 * @param timestamp an integer timestamp in milliseconds 
	 * @author JD
	 */
	IRReport(vector<int>, int);

	//TODO Report Destructor
	virtual ~IRReport();

	/**
	 * In order for an IRReport to be valid, it needs to
	 * contain twelve bytes of information and a non-zero
	 * timestamp.
	 * @return true if the report is valid, false otherwise.
	 * @author JD
	 */
	bool isValid();

	/**
	 * Timestamp getter
	 * @return the timestamp (in millisecs) of this report
	 * @author JD
	 */
	int getTimestamp() {return _timestamp;}

	/**
	 * Values getter
	 * @return a vector of size 12 with the data
	 * @author JD
	 */
	vector<int> getValues() {return _values;}
	
	/**
	 * Prints the report on one line to cout
	 * @author JD
	 */
	void print();
private:
	/**
	 * A vector of integers containing 12 integers, each of
	 * which represents one byte worth of information extracted
	 * from a wiimote.
	 * @author JD
	 */
	vector<int> _values;
	
	/**
	 * An integer containing the time at which the report was
	 * receiver for processing in milliseconds as returned
	 * by gettimeofday() from sys/time.h on linux
	 * @author JD
	 */
	int _timestamp;
};

#endif /*IRREPORT_H_*/
