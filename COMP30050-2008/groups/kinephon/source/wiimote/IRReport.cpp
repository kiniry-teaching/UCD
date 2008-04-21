#include "IRReport.h"
#include <vector>
#include <iostream>
using namespace std;

IRReport::IRReport(vector<int> values, int timestamp)
{
	_timestamp = timestamp;
	_values = values;
}

IRReport::~IRReport()
{
}

bool IRReport::isValid() 
{
	//A report is only valid when the vector has
	//12 elements and the stamp has a non-zero value
	if (_values.size() != 12 && _timestamp > 0) {
//		optional cout output...
//		cout << "size = " << _values.size() << " ";
		return false;
	} else {
		return true;
	}
}

void IRReport::print() 
{
	for (int i = 0; i < _values.size(); i++) {
		int item_value = _values.at(i);
		if (item_value > 99) {
			cout << " ";
		} else if (item_value < 10) {
			cout << "   ";
		} else {
			cout << "  ";
		}
		cout << item_value;
	}
	
	cout << " " << _timestamp << endl;
}
