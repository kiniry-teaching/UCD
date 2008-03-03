#include "Conductor.h"
#include <string>
#include <iostream>
using namespace std;

// Platform-dependent sleep routines.
#if defined(__WINDOWS_MM__)
  #include <windows.h>
  #define SLEEP( milliseconds ) Sleep( (DWORD) milliseconds ) 
#else // Unix variants
  #include <unistd.h>
  #define SLEEP( milliseconds ) usleep( (unsigned long) (milliseconds * 1000.0) )
#endif

/**
 * @author:	ED
 *
 * Demo test program for MidiPlayer.
 */

int main(){
	
	Conductor audio;
	if(!audio.initialize())
    	exit( EXIT_FAILURE ); 
   
    vector<uchar> melody(30);
    melody[0] = 76; melody[1] = 60;
    melody[2] = 75; melody[3] = 60;
    melody[4] = 76; melody[5] = 60;
    melody[6] = 75; melody[7] = 60;
    melody[8] = 76; melody[9] = 60;
    melody[10] = 71; melody[11] = 60;
    melody[12] = 74; melody[13] = 60;
    melody[14] = 72; melody[15] = 60;
    melody[16] = 69; melody[17] = 127;
    
    melody[18] = 33; melody[19] = 60;
    melody[20] = 40; melody[21] = 60;
    melody[22] = 45; melody[23] = 60;
    melody[24] = 60; melody[25] = 60;
    melody[26] = 64; melody[27] = 60;
    melody[28] = 69; melody[29] = 60;
    
    
    audio.setMelody(melody);
    int i = 0;
    while(i < 30){
    	audio.play();	
    	SLEEP(200);
    	i++;
    }	
    audio.pressPanicButton();
   
	return 0;
}
