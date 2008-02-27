#include "MidiPlayer.h"
#include "RtError.h"

MidiPlayer::MidiPlayer():
	_midiout(NULL),
	_connected(false),
	_defaultChannel(NULL),
	_rhythmChannel(NULL)
{}

MidiPlayer::~MidiPlayer()
{
	delete _midiout;
}

bool MidiPlayer::init(){
	// RtMidiOut constructor
	_midiout = new RtMidiOut();
  	
  	// Call function to select port.
  	cout << "\nWould you like to open a virtual output port? [y/N] ";

  	string keyHit;
  	getline( cin, keyHit );
  	if ( keyHit == "y" ) {
  		try{
    		_midiout->openVirtualPort();
  		}
    	catch ( RtError &error ) {
    		_connected = false;	
    	}
    	_connected = true;
  	}else{
		string portName;
  		unsigned int i = 0, nPorts = _midiout->getPortCount();
  		if ( nPorts == 0 ) {
  			_connected = false;
   		}
		if ( nPorts == 1 ) {
    		cout << "\nOpening " << _midiout->getPortName() << endl;
    		_connected = true;
  		}
  		else {
    		for ( i=0; i<nPorts; i++ ) {
      			portName = _midiout->getPortName(i);
      			cout << "  Output port #" << i << ": " << portName << '\n';
    		}
    		do {
      			cout << "\nChoose a port number: ";
      			cin >> i;
    		} while ( i >= nPorts );
  		}
  	  	cout << "\n";
  		_midiout->openPort( i );
  		_connected = true;
  	}
  	if(_connected){
  		_defaultChannel = new Channel(_midiout, 0);
  		_rhythmChannel = new Channel(_midiout, 9);
  		return true;
  	}
  	else{
  		return false;
  	}
}

void MidiPlayer::PlayNote(bool on, unsigned char pitch, unsigned char velocity){
	if(_connected){
		if(on)
			_defaultChannel -> Play( pitch, velocity );
		else
			_defaultChannel -> Release( pitch, velocity );
	}
}

// Plays or stops the given note on given channel
void MidiPlayer::PlayRhythm(bool on, unsigned char pitch, unsigned char velocity){
	if(_connected){
		if(on)
			_rhythmChannel -> Play( pitch, velocity );
		else
			_rhythmChannel -> Release( pitch, velocity );
	}
		

}
	

void MidiPlayer::ProgramChange(unsigned char channel, unsigned char program){
	if(_connected){
		_defaultChannel -> ProgramChange( program );
	}
}
	
void MidiPlayer::ControlChange(unsigned char channel, unsigned char function, unsigned char value){
	if(_connected){
		_defaultChannel -> ControlChange( function, value );

	}
}

//Just a demo
void MidiPlayer::Input(int tune){
	PlayNote(true, MIDDLE_F, 60);SLEEP ( 300 );PlayNote(false, MIDDLE_F, 60);
	PlayNote(true, MIDDLE_G, 60);SLEEP ( 300 );PlayNote(false, MIDDLE_G, 60);
	PlayNote(true, MIDDLE_A, 127);SLEEP( 700 );PlayNote(false, MIDDLE_A, 60);
	PlayNote(true, MIDDLE_A, 60);SLEEP ( 150 );PlayNote(false, MIDDLE_A, 60);
	PlayNote(true, MIDDLE_G, 60);SLEEP ( 150 );PlayNote(false, MIDDLE_G, 60);
	PlayNote(true, MIDDLE_F, 60);SLEEP ( 300 );PlayNote(false, MIDDLE_F, 60);
	PlayNote(true, MIDDLE_G, 127);SLEEP ( 700 );PlayNote(false, MIDDLE_G, 60);
	PlayNote(true, MIDDLE_A, 60);SLEEP ( 300 );PlayNote(false, MIDDLE_A, 60);
	PlayNote(true, MIDDLE_G, 60);SLEEP ( 300 );PlayNote(false, MIDDLE_G, 60);
	PlayNote(true, MIDDLE_F, 127);SLEEP ( 700 );PlayNote(false, MIDDLE_F, 60);
	PlayNote(true, MIDDLE_A, 60);SLEEP ( 300 );PlayNote(false, MIDDLE_A, 60);
	PlayNote(true, 72, 60);SLEEP ( 300 );PlayNote(false, 72, 60);
	PlayNote(true, 74, 127);SLEEP ( 700 );PlayNote(false, 74, 60);

}

