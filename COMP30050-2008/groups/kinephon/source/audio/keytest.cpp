#include "MidiPlayer.h"
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

/*
 * Author:	ED
 *
 * Demo test program for MidiPlayer.
 */
 
int main(){
	
	MidiPlayer* audio = 0;
	audio = new MidiPlayer();
	if(!audio->init())
    	exit( EXIT_FAILURE );
    
    audio->Input(0);
    	
	
	return 0;
}
