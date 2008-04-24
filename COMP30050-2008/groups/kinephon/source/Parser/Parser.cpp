#include "Parser.h"
#include <vector>

Parser::Parser()
{
	binaryPosition = 0;
	for(int i=0; i<12; i++)
		reportData[i] = 0;
	for(int i=0; i<8; i++)
	{
		MSB_Size_Array[i] = 0;
	}
	for(int i=0; i<4; i++)
		control[i] = 0;

}


Parser::Parser(IParserRecorder* ipr)
{
	iprp = ipr;
	binaryPosition = 0;
	for(int i=0; i<12; i++)
		reportData[i] = 0;
	for(int i=0; i<8; i++)
		MSB_Size_Array[i] = 0;
	for(int i=0; i<4; i++)
		control[i] = 0;	
}

void Parser::supplyReport(IRReport report)
{
	int tmp[3];
	
	int c_switch=0;
	for(int j=0;j<12;j+=3)
	{
		if(j==0)c_switch=0;
		if(j==3)c_switch=1;
		if(j==6)c_switch=2;
		if(j==9)c_switch=3;

		tmp[0] = report.getValues()[j];
		tmp[1] = report.getValues()[j+1];
		tmp[2] = report.getValues()[j+2];

		if(tmp[0]==255 || tmp[1]==255 || tmp[2]==255)
		{
			control[c_switch]=1;
			iprp->control(control[c_switch],c_switch+1);
		}
		else
		{
			control[c_switch]=0;
			iprp->control(control[c_switch],c_switch+1);
		}

		if(control[c_switch]==0)
		{
			for(int i = 0 ; i < 8; i++)
			{
				MSB_Size_Array[i] = 0;
			}
			
			populate(tmp[2]);
			tmp[0] += MSB_Extract(MSB_Size_Array[2],MSB_Size_Array[3]);
			tmp[1] += MSB_Extract(MSB_Size_Array[0],MSB_Size_Array[1]);
			tmp[2] = Size_Extract();
			iprp->record(c_switch+1, tmp[0], tmp[1], tmp[2], report.getTimestamp());
		}
	}
}

void Parser::populate(int number) {
	int array[] = {128, 64, 32, 16, 8, 4, 2, 1};
	for (int i=0; i<=7; i++)
	{
		if (number >= array[i])
		{
			MSB_Size_Array[i] = 1;
			number -= array[i];
		}
	}
}

int Parser::MSB_Extract(int first,int second)
{
	if(first==1)
		first=(int)pow(2.0,9.0);
	if(second==1)
		second=(int)pow(2.0,8.0);
	return first+second;
}

int Parser::Size_Extract()
{
	int total=0;
	for(int i=4;i<7;i++)
	{
		if(MSB_Size_Array[i]==1)
			total+=(int)pow(2.0,i);
	}
	return total;	
}
