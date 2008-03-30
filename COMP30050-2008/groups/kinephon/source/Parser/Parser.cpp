#include "Parser.h"

Parser::Parser()
{
	x=0,y=0,size=0;
}

void Parser::parser(string in, int size_of)
{
	int counter = 0;
	for(int i=0; i+4<size_of; i++)
	{
		if(in[i]=='[' && in[i+2]==',')
		{
			array[counter] = atoi(in.substr(i+1, i+1).data());
			counter++;
		}
		else
		{
			if(in[i]=='[' && in[i+3]==',')
			{
				array[counter] = atoi(in.substr(i+1, i+2).data());
				counter++;
			}
			else
			{
				if(in[i]=='[' && in[i+4]==',')
				{
					array[counter] = atoi(in.substr(i+1, i+3).data());
					counter++;
				}	
			}
		}
		
		if(in[i]==' ' && in[i+2]==',')
		{
			array[counter] = atoi(in.substr(i+1, i+1).data());
			counter++;
		}
		else
		{
			if(in[i]==' ' && in[i+3]==',' || in[i+3]==']')
			{
				array[counter] = atoi(in.substr(i+1, i+2).data());
				counter++;
			}
			else
			{
				if(in[i]==' ' && in[i+4]==',' || in[i+4]==']')
				{
					array[counter] = atoi(in.substr(i+1, i+3).data());
					counter++;
				}	
			}
		}
	}
	for(int j=0;j<12;j++)
	{
		cout << array[j] << " ";
	}
	cout << endl;
}

void Parser::provide()
{
	
}

Parser::~Parser()
{
}
