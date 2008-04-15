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


bool MidiPlayer::initialize(bool recording, string portNm) {
	// RtMidiOut constructor
	midiout_ = new RtMidiOut();
  	
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
            if (portName.compare(0, portNm.length(), portNm.data()) == 0){
                portNumber = i;
            }
            
    	}
  	}
	midiout_->openPort(portNumber);
	isConnected_ = true;
# endif
#if defined(__WINDOWS_MM__)//for testing purposes only, since some are using Windows
    cout << "\nWould you like to open a virtual output port? [y/N] ";
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
    else {
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
          chordChannel_->release(chords_[0], deltaTime);        
          chordChannel_->release(chords_[1], deltaTime);
          chordChannel_->release(chords_[2], deltaTime);
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
                chordChannel_->release(chords_[0], deltaTime);        
                chordChannel_->release(chords_[1], deltaTime);
                chordChannel_->release(chords_[2], deltaTime);
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
