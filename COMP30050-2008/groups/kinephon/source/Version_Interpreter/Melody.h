#ifndef MELODY_H_
#define MELODY_H_
#include <vector>
#include "type.h"
#include "Conductor.h"

using namespace std;
using namespace audio;

class Melody
{
public:
	Melody();
	virtual ~Melody();
	static  vector<uchar> melody1;
	static  vector<uchar> melody2;
	static  vector<uchar> melody3;
	static vector< vector<uchar> > meloding;
	static void intialised();
    
};

inline void Melody::intialised(){
	
	    meloding.push_back(melody1);
	    meloding.push_back(melody2);
	    meloding.push_back(melody3);
	    
	    melody1[0] = 60; melody1[1] = 127;
	    melody1[2] = NO_NOTE; melody1[3] = 60;
	    melody1[4] = 64; melody1[5] = 60;
	    melody1[6] = 67; melody1[7] = 60;
	    melody1[8] = 69; melody1[9] = 60;
	    melody1[10] = 70; melody1[11] = 127;
	    melody1[12] = NO_NOTE; melody1[13] = 60;
	    melody1[14] = 69; melody1[15] = 60;
	    melody1[16] = 67; melody1[17] = 127;
	    melody1[18] = 64; melody1[19] = 60;
	    
	    
	     melody2[0] = 65; melody2[1] = 127;
	    melody2[2] = NO_NOTE; melody2[3] = 60;
	    melody2[4] = 69; melody2[5] = 60;
	    melody2[6] = 72; melody2[7] = 60;
	    melody2[8] = 74; melody2[9] = 60;
	    melody2[10] = 75; melody2[11] = 127;
	    melody2[12] = NO_NOTE; melody2[13] = 60;
	    melody2[14] = 74; melody2[15] = 60;
	    melody2[16] = 72; melody2[17] = 127;
	    melody2[18] = 69; melody2[19] = 60;
	    
	     melody3[0] = 67; melody3[1] = 127;
	    melody3[2] = NO_NOTE; melody3[3] = 60;
	    melody3[4] = 71; melody3[5] = 60;
	    melody3[6] = 74; melody3[7] = 60;
	    melody3[8] = 76; melody3[9] = 60;
	    melody3[10] = 77; melody3[11] = 127;
	    melody3[12] = NO_NOTE; melody3[13] = 60;
	    melody3[14] = 76; melody3[15] = 60;
	    melody3[16] = 74; melody3[17] = 127;
	    melody3[18] = 71; melody3[19] = 60;
	   
}
#endif /*MELODY_H_*/
