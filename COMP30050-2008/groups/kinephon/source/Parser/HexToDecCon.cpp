#include "HexToDecCon.h"

HexToDecCon::HexToDecCon(){}

float HexToDecCon::apply(char *a)
{
	int hex = 1, hex1 = 16, conversion = 0;
	for(int i=strlen(a)-1; i > -1; i--)
	{
		char tmp = charAt(a, i);
		if(tmp <= 102 && tmp >= 97 || tmp <= 70 && tmp >= 65 || tmp >=48 && tmp <=57)
		{
			conversion += charConvert(tmp)*hex;
		}
		else
			cout << "Out of range ASCII provided for decimal conversion :-p" << endl;
		hex *= hex1;
	}
	return conversion;
}

char HexToDecCon::charAt(char *string, int place)
{
	return(string[place]);	
}

int HexToDecCon::charConvert(char a)
{
	switch(a)
	{
		case 'a': return A;
		case 'b': return B;
		case 'c': return C;
		case 'd': return D;
		case 'e': return E;
		case 'f': return F;
		case 'A': return A;
		case 'B': return B;
		case 'C': return C;
		case 'D': return D;
		case 'E': return E;
		case 'F': return F;
		case '1': return 1;
		case '2': return 2;
		case '3': return 3;
		case '4': return 4;
		case '5': return 5;
		case '6': return 6;
		case '7': return 7;
		case '8': return 8;
		case '9': return 9;
		
	}
	return a;
}

HexToDecCon::~HexToDecCon()
{
}
