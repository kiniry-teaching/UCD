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
  	if (isConnected_){
        try {//sending messages, so catch expections
            if (recording) {//set up MidiRecorder
                recorder_ = new MidiRecorder();
                try {
                    recorder_->openFile(1);
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
void MidiPlayer::panic() {
	if(isConnected_) {
        try {
		  leadChannel_->release();
          accompanyChannel_->release();
          chordChannel_->release(chords_[0]);        
          chordChannel_->release(chords_[1]);
          chordChannel_->release(chords_[2]);
          percussionChannel_->release();
        }
        catch (RtError &error) {}
	}
}

//release notes on channel
void MidiPlayer::releaseChannel(Channels channel) {
    if(isConnected_) {
        try {
            if(channel == CHANNEL_LEAD)
                leadChannel_->release();
            else if(channel == CHANNEL_ACCOMPANY)
                accompanyChannel_->release();
            else if(channel == CHANNEL_CHORD){
                chordChannel_->release(chords_[0]);        
                chordChannel_->release(chords_[1]);
                chordChannel_->release(chords_[2]);
            }
            else if(channel == CHANNEL_PERCUSSION)
                percussionChannel_->release();
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
void MidiPlayer::playLead(uchar pitch, uchar velocity) {
    if(isConnected_) 
        try {
            leadChannel_->play(pitch, velocity, 0);
        }
        catch (RtError &error) {}
}
	
void MidiPlayer::playAccompaniment(uchar pitch, uchar velocity) {
    if(isConnected_)
        try {
            accompanyChannel_->play(pitch, velocity, 0);
        }
        catch (RtError &error) {}
}
	
void MidiPlayer::playChord(uchar chord, uchar velocity) {
    if(isConnected_)
        try {
            chordChannel_->play(chord, velocity, 0);
            chords_[0] = chord;
            chordChannel_->play(chord + 4, velocity, 0);
            chords_[1] = chord + 4;
            chordChannel_->play(chord + 7, velocity, 0);
            chords_[2] = chord + 7;
        }
        catch (RtError &error) {}
}
	
void MidiPlayer::playPercussion(uchar pitch, uchar velocity) {
    if(isConnected_)
        try {
            percussionChannel_->play(pitch, velocity, 0);
        }
        catch (RtError &error) {}
}

void MidiPlayer::playNote(Channels channel, uchar pitch, uchar velocity) {
    if (isConnected_) {
        try {
            if (channel == CHANNEL_LEAD)
                leadChannel_->play(pitch, velocity, 0);
            else if(channel == CHANNEL_ACCOMPANY)
                accompanyChannel_->play(pitch, velocity, 0);
            else if(channel == CHANNEL_CHORD)
                chordChannel_->play(pitch, velocity, 0);
            else if(channel == CHANNEL_PERCUSSION)
                percussionChannel_->play(pitch, velocity, 0);  
        }
        catch (RtError &error) {}
    }
}

void MidiPlayer::releaseNote(Channels channel, uchar pitch) {
    if (isConnected_) {
        try {
            if (channel == CHANNEL_LEAD)
                leadChannel_->release(pitch);
            else if(channel == CHANNEL_ACCOMPANY)
                accompanyChannel_->release(pitch);
            else if(channel == CHANNEL_CHORD)
                chordChannel_->release(pitch);
            else if(channel == CHANNEL_PERCUSSION)
                percussionChannel_->release(pitch);  
        }
        catch (RtError &error) {}
    }
}

void MidiPlayer::otherOptions() {}

}
