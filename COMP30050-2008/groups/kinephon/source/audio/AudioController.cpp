#include "AudioController.h"
#include "RtError.h"

AudioController::AudioController():
	midiout(NULL),
	message(3)
{
	// RtMidiOut constructor
	midiout = new RtMidiOut();
  	
  	// Call function to select port.
  	cout << "\nWould you like to open a virtual output port? [y/N] ";

  	string keyHit;
  	getline( cin, keyHit );
  	if ( keyHit == "y" ) {
    	midiout->openVirtualPort();
    	
  	}else{
		string portName;
  		unsigned int i = 0, nPorts = midiout->getPortCount();
  		if ( nPorts == 0 ) {
    		throw RtError("No output ports available", RtError::NO_DEVICES_FOUND);
   		}
		if ( nPorts == 1 ) {
    		cout << "\nOpening " << midiout->getPortName() << endl;
  		}
  		else {
    		for ( i=0; i<nPorts; i++ ) {
      			portName = midiout->getPortName(i);
      			cout << "  Output port #" << i << ": " << portName << '\n';
    		}
    		do {
      			cout << "\nChoose a port number: ";
      			cin >> i;
    		} while ( i >= nPorts );
  		}
  	  	cout << "\n";
  		midiout->openPort( i );
  	}
	
}

AudioController::~AudioController()
{
	delete midiout;
}



void AudioController::makeBeep(bool on, unsigned char channel, unsigned char pitch){
if(on){

  message[0] = 144 + channel;
  message[1] = pitch;
  message[2] = 90;
  midiout->sendMessage( &message );
}
else{
  // Note Off: 128, 64, 40
  message[0] = 128 + channel;
  message[1] = pitch;
  message[2] = 40;
  midiout->sendMessage( &message );
}
}

void AudioController::changeProgram(unsigned char channel, unsigned char program){
	vector<unsigned char> mssg;
	mssg.push_back( 192 + channel );
  	mssg.push_back( program );
  
  midiout->sendMessage( &mssg );
}
	
void AudioController::modeTest(unsigned char channel, unsigned char function, unsigned char value){
	message[0] = 176  + channel;
  	message[1] = function;
  	message[2] = value;
  	midiout->sendMessage( &message );
}
