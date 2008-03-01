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
    
    vector<uchar> melody;
    melody.push_back(60);
    melody.push_back(61);
    melody.push_back(62);
    melody.push_back(63);
    audio.setMelody(&melody);
    int i = 0;
    while(i < 8){
    	audio.play();	
    	SLEEP(500);
    	i++;
    }	
    audio.pressPanicButton();
	return 0;
}
