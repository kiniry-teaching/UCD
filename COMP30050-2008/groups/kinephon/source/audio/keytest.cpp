#include "AudioController.h"
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

int main(){
	
	AudioController* audio = 0;
	
	try {
    	audio = new AudioController();
  	}
  	catch ( RtError &error ) {
    	error.printMessage();
    	exit( EXIT_FAILURE );
  	}
  	audio->changeProgram(0, 1);
  	
	audio->modeTest(0,7,50);
	
	audio->modeTest(0,64,100);
	
  	for(int i = 0; i < 10; i++){
    	
  		// Note On: 144, 64, 90
  		audio->makeBeep(true, 0, 64 + i);
		//audio->makeBeep(true, 1, 64 + i);
  		SLEEP( 500 );

  		// Note Off: 128, 64, 40
  		audio->makeBeep(false, 0, 64 + i);
  		//audio->makeBeep(false, 1, 64 + i);
    }

	return 0;
}
