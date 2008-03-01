#include "MidiPlayer.h"


MidiPlayer::MidiPlayer():
	midiout_(NULL),
	isConnected_(false),
	leadChannel_(NULL)
{}

MidiPlayer::~MidiPlayer()
{
	delete midiout_;
}

//TODO: initialize all channels
bool MidiPlayer::initialize(){
	// RtMidiOut constructor
	midiout_ = new RtMidiOut();
  	
  	// Call function to select port.
  	cout << "\nWould you like to open a virtual output port? [y/N] ";

  	string keyHit;
  	getline( cin, keyHit );
  	if ( keyHit == "y" ) {
  		try{
    		midiout_->openVirtualPort();
  		}
    	catch ( RtError &error ) {
    		isConnected_ = false;	
    	}
    	isConnected_ = true;
  	}else{
		string portName;
  		unsigned int i = 0, nPorts = midiout_->getPortCount();
  		if ( nPorts == 0 ) {
  			isConnected_ = false;
   		}
		if ( nPorts == 1 ) {
    		cout << "\nOpening " << midiout_->getPortName() << endl;
    		isConnected_ = true;
  		}
  		else {
    		for ( i=0; i<nPorts; i++ ) {
      			portName = midiout_->getPortName(i);
      			cout << "  Output port #" << i << ": " << portName << '\n';
    		}
    		do {
      			cout << "\nChoose a port number: ";
      			cin >> i;
    		} while ( i >= nPorts );
  		}
  	  	cout << "\n";
  		midiout_->openPort( i );
  		isConnected_ = true;
  	}
  	if(isConnected_){
  		leadChannel_ = new Channel(midiout_, 0);
  		return true;
  	}
  	else{
  		return false;
  	}
}

//release all notes
void MidiPlayer::panic(){
	if(isConnected_){
		leadChannel_ -> release();
	}
}

bool MidiPlayer::setRecording(bool setOn){}
	
void MidiPlayer::sendSysEx(int message, int value){}
	
void MidiPlayer::sendChannelMode(uchar mode ){}
	
void MidiPlayer::sendControlChange(uchar channel, uchar function, uchar value){
	if(isConnected_){
		leadChannel_ -> setControl( function, value );

	}
}
	
void MidiPlayer::sendProgramChange(uchar channel, uchar program){
	if(isConnected_){
		leadChannel_ -> setProgram( program );
	}
}
	
void MidiPlayer::playLead(uchar pitch, uchar velocity){}
	
void MidiPlayer::playAccompaniment(uchar pitch, uchar velocity){}
	
void MidiPlayer::playChord(uchar chord, uchar velocity){}
	
void MidiPlayer::playPercussion(uchar pitch, uchar velocity){}

void MidiPlayer::playNote(Channels channel, uchar pitch, uchar velocity){
	if(isConnected_){
		
			leadChannel_ -> play( pitch, velocity, 0 );
		
	}
}
	
void MidiPlayer::otherOptions(){}
	

	


/*
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
*/
