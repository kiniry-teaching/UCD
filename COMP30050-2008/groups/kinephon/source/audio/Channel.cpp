#include "Channel.h"
namespace audio
{
Channel::Channel(RtMidiOut* midi, int no, MidiRecorder* recorder):
	channelNo_(no),
	programNo_(0),//default acoustic grand piano
	midiout_(midi),
    recorder_(recorder)
{
	//set acoustic grand piano as default
	vector<uchar> message(2);
	message[0] = 192 + channelNo_;
	message[1] = programNo_;
  	midiout_->sendMessage(&message);
  	if (recorder_ != NULL)
        recorder_->write(message, 0);       
    
    
  	for (int i = 0; i < 93; i++)
		controls_[i] = 0;
		
  	// Channel Volume (cc#7), default max volume
  	message[0] = 176 + channelNo_;
	message[1] = 7;
	message.push_back(127);
	midiout_->sendMessage(&message);
	controls_[7] = 127;		
	if (recorder_ != NULL);
        recorder_->write(message, 0);       
    
}

Channel::~Channel() {
    release(0);
}

// Returns the mode of the specified function. 
uchar Channel::getControl(uchar control) {
	return controls_[control];
}

// Returns the program 
uchar Channel::getProgram() {
	return programNo_;
}
	
//Adjusts this channel's settings 
void Channel::setControl(uchar function, uchar value) {
	controls_[function] = value;
	vector<uchar> message(3);
  	message[0] = 176 + channelNo_;
  	message[1] = function;
  	message[2] = value;
	midiout_->sendMessage(&message);
    
    if (recorder_ != NULL);
        recorder_->write(message, 0);       
    
}
	 
//Change the instrument.
void Channel::setProgram(uchar program) {
	programNo_ = program;
	vector<uchar> message(2);
	message[0] = 192 + channelNo_;
	message[1] = programNo_;
  	midiout_->sendMessage(&message);

    if (recorder_ != NULL);
       recorder_->write(message, 0);       
    
}
	
//Plays the given note in default octave.
void Channel::play(uchar pitch, uchar velocity, ulong deltaTime) {
	note_[0] = pitch;
	note_[1] = velocity;
	vector<uchar> message(3);
  	message[0] = 144 + channelNo_;
  	message[1] = pitch;
  	message[2] = velocity;
  	midiout_->sendMessage(&message);
    
    if (recorder_ != NULL)
        recorder_->write(message, deltaTime);       
       
}
	
	
//Stops the playing note.
void Channel::release(ulong deltaTime) {
	vector<uchar> message(3);
	message[0] = 128 + channelNo_;
	message[1] = note_[0];
  	message[2] = note_[1];
  	midiout_->sendMessage(&message);
    
    if (recorder_ != NULL)
        recorder_->write(message, deltaTime);       
        
}

void Channel::release(uchar pitch, ulong deltaTime) {
    vector<uchar> message(3);
    message[0] = 128 + channelNo_;
    message[1] = pitch;
    message[2] = note_[1];
    midiout_->sendMessage(&message);
    
    if (recorder_ != NULL)
        recorder_->write(message, deltaTime);       
    
}

  

}
