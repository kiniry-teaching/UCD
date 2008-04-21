#include "Parser.h"

Parser::Parser()
{
	binaryPosition = 0;
	for(int i=0; i<12; i++)
		reportData[i] = 0;
	for(int i=0; i<8; i++)
	{
		MSB_Size_Array[i] = 0;
		binaryX[i] = 0;
		binaryY[i] = 0;
	}
	for(int i=0; i<4; i++)
		control[i] = 0;
		
}


Parser::Parser(IParserRecorder* ipr)
{
	binaryPosition = 0;
	for(int i=0; i<12; i++)
		reportData[i] = 0;
	for(int i=0; i<8; i++)
		MSB_Size_Array[i] = 0;
	for(int i=0; i<4; i++)
		control[i] = 0;	
}

/*
 * This is just used for parsing the test data.
 */

void Parser::parser(string in, int size_of)
{
	int counter = 0;
	for(int i=0; i+4<size_of; i++)
	{
		if(in[i]=='[' && in[i+2]==',')
		{
			reportData[counter] = atoi(in.substr(i+1, i+1).data());
			counter++;
		}
		else
		{
			if(in[i]=='[' && in[i+3]==',')
			{
				reportData[counter] = atoi(in.substr(i+1, i+2).data());
				counter++;
			}
			else
			{
				if(in[i]=='[' && in[i+4]==',')
				{
					reportData[counter] = atoi(in.substr(i+1, i+3).data());
					counter++;
				}	
			}
		}
		
		if(in[i]==' ' && in[i+2]==',')
		{
			reportData[counter] = atoi(in.substr(i+1, i+1).data());
			counter++;
		}
		else
		{
			if(in[i]==' ' && in[i+3]==',' || in[i+3]==']')
			{
				reportData[counter] = atoi(in.substr(i+1, i+2).data());
				counter++;
			}
			else
			{
				if(in[i]==' ' && in[i+4]==',' || in[i+4]==']')
				{
					reportData[counter] = atoi(in.substr(i+1, i+3).data());
					counter++;
				}	
			}
		}
	}
	provide();
}

void Parser::provide()
{
	int tmp[3];
	tmp[0]=0,tmp[1]=0,tmp[2]=0;
	int c_switch=0;
	for(int j=0;j<12;j+=3)
	{
		if(j==0)c_switch=0;
		if(j==3)c_switch=1;
		if(j==6)c_switch=2;
		if(j==9)c_switch=3;
		
		tmp[0] = reportData[j];
		tmp[1] = reportData[j+1];
		tmp[2] = reportData[j+2];
		
		if(tmp[0]==255 || tmp[1]==255 || tmp[2]==255)
			control[c_switch]=1;
		else
			control[c_switch]=0;
		
		//control(control[0],k+1);
			
		if(control[c_switch]==0)
		{
		  	binary(tmp[2]);
		  	binaryPosition = 0;
		  	for(int i=0;i<8;i++)
		  		cout << MSB_Size_Array[i];
		  	cout << endl;
		  	tmp[0] += MSB_Extract(MSB_Size_Array[2],MSB_Size_Array[3]);
		  	tmp[1] += MSB_Extract(MSB_Size_Array[0],MSB_Size_Array[1]);
		  	tmp[2] = Size_Extract();
		  	setX(tmp[0]);
		  	setY(tmp[1]);
		  	cout << " REPORTID: " << c_switch+1 << " X: " << tmp[0] << " Y: " << tmp[1] << " Size: " << tmp[2] <<  endl;
		}
	}
	for(int k=0;k<4;k++)
	{
		cout << control[k] << " ";
	}
	cout << endl;
}

void Parser::binary(int number) {
	int remainder;

	if(number <= 1 && binaryPosition<=7) {
		MSB_Size_Array[binaryPosition++] = number;
		return;
	}
	else
	{
		remainder = number%2;
		binary(number >> 1);    
		MSB_Size_Array[binaryPosition++] = remainder;
	}
}

int Parser::MSB_Extract(int first,int second)
{
	if(first==1)
		first=(int)pow(2.0,8.0);
	if(second==1)
		second=(int)pow(2.0,9.0);
	return first+second;
}

int Parser::Size_Extract()
{
	int counterWeight=7,total=0;
	for(int i=7;i>3;i--)
	{
		if(MSB_Size_Array[i]==1)
			total+=(int)pow(2.0,i-(double)counterWeight);
		counterWeight-=2;
	}
	return total;	
}

Parser::~Parser()
{
}
