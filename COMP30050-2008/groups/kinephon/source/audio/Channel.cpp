#include "Channel.h"

Channel::Channel(RtMidiOut* midi, int no):
	channelNo_(no),
	programNo_(1),
	octaveNo_(0),
	midiout_(midi)
{
	//TODO: set default settings
	vector<uchar> message(2);
	message[0] = 192 + channelNo_;
	message[1] = programNo_;
  	midiout_->sendMessage( &message );
  	
  	message[0] = 176 + channelNo_;
	message[1] = 7;
	message.push_back(127);
	midiout_->sendMessage( &message );
  	
}

Channel::~Channel()
{
}

// Returns the mode of the specified function. 
uchar Channel::getControl(uchar control){
	return 0u;
}

// Returns the program 
uchar Channel::getProgram(){
	return 0u;
}
	
//Adjusts this channel's settings 
void Channel::setControl(uchar function, uchar value){}
	 
//Change the instrument.
void Channel::setProgram(uchar program){}
	
//Plays the given note in default octave.
void Channel::play(uchar note, uchar velocity, int octave){
	vector<uchar> message(3);
  	message[0] = 144 + channelNo_;
  	message[1] = note;
  	message[2] = velocity;
  	midiout_->sendMessage( &message );
	note_[0] = note;
	note_[1] = velocity;
}
	
	
//Stops the playing note.
void Channel::release(){
	vector<uchar> message(3);
	message[0] = 128 + channelNo_;
	message[1] = note_[0];
  	message[2] = note_[1];
  	midiout_->sendMessage( &message );
	

}

