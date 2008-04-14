#include "MidiPlayer.h"

namespace audio
{
    
MidiPlayer::MidiPlayer():
	midiout_(NULL),
    recorder_(NULL),
    chords_(3),
	isConnected_(false),
	leadChannel_(NULL),
	chordChannel_(NULL),
	accompanyChannel_(NULL),
	percussionChannel_(NULL)
{}

//delete all dynamic data structures
MidiPlayer::~MidiPlayer() {
	delete midiout_;
    delete leadChannel_;
    delete chordChannel_;
    delete accompanyChannel_;
    delete percussionChannel_;
    
    //close file first, before we delete the class, at least try it...
    try {
        recorder_->closeFile();
    }
    catch (...) {}
    if (recorder_ != NULL)
        delete recorder_;
}


bool MidiPlayer::initialize(bool recording) {
	// RtMidiOut constructor
	midiout_ = new RtMidiOut();
  	
  	// Call function to select port.
    //NOTE: THIS CHOICE OF PORTS ONLY WORKS FOR LINUX WHEN USING FLUIDSYNTH
    //Output port #1: Synth input port (5597:0)
    //TODO: we have to do this ourselves...
    //1. get number ports available
    //2. check each for some sort of ID
    //3. if we find the fluidsynth one, open that
  	/*cout << "\nWould you like to open a virtual output port? [y/N] ";
    */
  	
#if defined(__LINUX_ALSASEQ__)

	string portName;
    int portNumber = 0;
  	unsigned int i = 0, nPorts = midiout_->getPortCount();
  	if (nPorts == 0) {
  		isConnected_ = false;
   	}
	if (nPorts == 1) {
    	cout << "\nOpening " << midiout_->getPortName() << endl;
    	isConnected_ = true;
  	}
  	else {
    	for (i=0; i<nPorts; i++) {
        	portName = midiout_->getPortName(i);
            cout << "Checking port number " << i << "has name>"<< portName << "<"<< endl;
        	//cout << "  Output port #" << i << ": " << portName << '\n';
            
            //only compare first 16 characters, assuming most recent synth port is last...
            if (portName.compare(0, 16, "Synth input port") == 0){
                portNumber = i;
                cout << "  Output port #" << i << ": " << portName << '\n';
            }
            
    	}
  	}
  	cout << "\n";
  		midiout_->openPort(portNumber);
        
  		isConnected_ = true;
# endif
#if defined(__WINDOWS_MM__)
    string keyHit;
    getline(cin, keyHit);
    if (keyHit == "y") {
        try {
            midiout_->openVirtualPort();
        }
        catch (RtError &error) {
            isConnected_ = false;   
        }
        isConnected_ = true;
    }
    else {*/
    string portName;
    unsigned int i = 0, nPorts = midiout_->getPortCount();
    if (nPorts == 0) {
        isConnected_ = false;
    }
    if (nPorts == 1) {
        cout << "\nOpening " << midiout_->getPortName() << endl;
        isConnected_ = true;
    }
    else {
        for (i=0; i<nPorts; i++) {
            portName = midiout_->getPortName(i);
            cout << "  Output port #" << i << ": " << portName << '\n';
        }
        do {
           cout << "\nChoose a port number: ";
           cin >> i;
        } while (i >= nPorts);
    }
    cout << "\n";
        midiout_->openPort(i);
        isConnected_ = true;
    }
#endif
  	if (isConnected_){
        try {//sending messages, so catch expections
            if (recording) {//set up MidiRecorder
                recorder_ = new MidiRecorder();
                try {
                    recorder_->openFile();
                }
                catch (...) {
                    //if we cannot open the file, no point passing it to the Channels
                    delete recorder_;
                    recorder_ = NULL;
                }
            } 
            leadChannel_ = new Channel(midiout_, 0, recorder_);
            accompanyChannel_ = new Channel(midiout_, 1, recorder_);
            chordChannel_ = new Channel(midiout_, 2, recorder_);
            percussionChannel_ = new Channel(midiout_, 3, recorder_);
  		    return true;
        }
        catch (RtError &error) {
            return false;
        }
  	}
  	else {
  		return false;
  	}
}

//release all notes
void MidiPlayer::panic(ulong deltaTime) {
	if(isConnected_) {
        try {
		  leadChannel_->release(deltaTime);
          accompanyChannel_->release(deltaTime);
          chordChannel_->release(chords_[0]);        
          chordChannel_->release(chords_[1]);
          chordChannel_->release(chords_[2]);
          percussionChannel_->release(deltaTime);
        }
        catch (RtError &error) {}
	}
}

//release notes on channel
void MidiPlayer::releaseChannel(Channels channel, ulong deltaTime) {
    if(isConnected_) {
        try {
            if(channel == CHANNEL_LEAD)
                leadChannel_->release(deltaTime);
            else if(channel == CHANNEL_ACCOMPANY)
                accompanyChannel_->release(deltaTime);
            else if(channel == CHANNEL_CHORD){
                chordChannel_->release(chords_[0]);        
                chordChannel_->release(chords_[1]);
                chordChannel_->release(chords_[2]);
            }
            else if(channel == CHANNEL_PERCUSSION)
                percussionChannel_->release(deltaTime);
        }
        catch (RtError &error) {}
    }   
}

bool MidiPlayer::setRecording(bool setOn) {
	return false;
}
	
	
//TODO: find out which ones we will use
void MidiPlayer::sendChannelMode(uchar mode ) {}
	
void MidiPlayer::sendControlChange(Channels channel, uchar function, uchar value) {
	if (isConnected_) {
        try {
		  if (channel == CHANNEL_LEAD)
		      leadChannel_->setControl(function, value);
		  else if(channel == CHANNEL_ACCOMPANY)
		      accompanyChannel_->setControl(function, value);
		  else if(channel == CHANNEL_CHORD)
		      chordChannel_->setControl(function, value);
		  else if(channel == CHANNEL_PERCUSSION)
		      percussionChannel_->setControl(function, value);	
        }
        catch (RtError &error) {}	   
    }
}
	
void MidiPlayer::sendProgramChange(Channels channel, uchar program) {
	if (isConnected_) {
        try {
            if (channel == CHANNEL_LEAD)
                leadChannel_->setProgram(program);
            else if(channel == CHANNEL_ACCOMPANY)
                accompanyChannel_->setProgram(program);
            else if(channel == CHANNEL_CHORD)
               chordChannel_->setProgram(program);
            else if(channel == CHANNEL_PERCUSSION)
                percussionChannel_->setProgram(program);  
        }
        catch (RtError &error) {}
    }
}
	
//TODO: figure out what to do with the octave
void MidiPlayer::playLead(uchar pitch, uchar velocity, ulong deltaTime) {
    if(isConnected_) 
        try {
            leadChannel_->play(pitch, velocity, deltaTime);
        }
        catch (RtError &error) {}
}
	
void MidiPlayer::playAccompaniment(uchar pitch, uchar velocity, ulong deltaTime) {
    if(isConnected_)
        try {
            accompanyChannel_->play(pitch, velocity, deltaTime);
        }
        catch (RtError &error) {}
}
	
void MidiPlayer::playChord(uchar chord, uchar velocity, ulong deltaTime) {
    if(isConnected_)
        try {
            chordChannel_->play(chord, velocity, deltaTime);
            chords_[0] = chord;
            chordChannel_->play(chord + 4, velocity, deltaTime);
            chords_[1] = chord + 4;
            chordChannel_->play(chord + 7, velocity, deltaTime);
            chords_[2] = chord + 7;
        }
        catch (RtError &error) {}
}
	
void MidiPlayer::playPercussion(uchar pitch, uchar velocity, ulong deltaTime) {
    if(isConnected_)
        try {
            percussionChannel_->play(pitch, velocity, deltaTime);
        }
        catch (RtError &error) {}
}

void MidiPlayer::playNote(Channels channel, uchar pitch, uchar velocity, ulong deltaTime) {
    if (isConnected_) {
        try {
            if (channel == CHANNEL_LEAD)
                leadChannel_->play(pitch, velocity, deltaTime);
            else if(channel == CHANNEL_ACCOMPANY)
                accompanyChannel_->play(pitch, velocity, deltaTime);
            else if(channel == CHANNEL_CHORD)
                chordChannel_->play(pitch, velocity, deltaTime);
            else if(channel == CHANNEL_PERCUSSION)
                percussionChannel_->play(pitch, velocity, deltaTime);  
        }
        catch (RtError &error) {}
    }
}

void MidiPlayer::releaseNote(Channels channel, uchar pitch, ulong deltaTime) {
    if (isConnected_) {
        try {
            if (channel == CHANNEL_LEAD)
                leadChannel_->release(pitch, deltaTime);
            else if(channel == CHANNEL_ACCOMPANY)
                accompanyChannel_->release(pitch, deltaTime);
            else if(channel == CHANNEL_CHORD)
                chordChannel_->release(pitch, deltaTime);
            else if(channel == CHANNEL_PERCUSSION)
                percussionChannel_->release(pitch, deltaTime);  
        }
        catch (RtError &error) {}
    }
}

void MidiPlayer::otherOptions() {}

}
