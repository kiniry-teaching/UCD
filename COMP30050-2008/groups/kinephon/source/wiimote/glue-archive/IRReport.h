#ifndef IRREPORT_H_
#define IRREPORT_H_
#include <vector>
using namespace std;

class IRReport
{
public:
	IRReport(vector<int>, int);
	virtual ~IRReport();
	bool isValid();
	int getTimestamp() {return _timestamp;}
	vector<int> getValues() {return _values;}
	void print();
private:
	vector<int> _values;
	int _timestamp;
};

#endif /*IRREPORT_H_*/
