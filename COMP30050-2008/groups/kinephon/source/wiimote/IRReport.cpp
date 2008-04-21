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
	if (_values.size() != 12) {
		cout << "size = " << _values.size() << " ";
		return false;
	} else {
		return true;
	}
	//TODO check for something else as well?
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
