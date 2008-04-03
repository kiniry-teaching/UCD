#include "Channel.h"
namespace audio
{
Channel::Channel(RtMidiOut* midi, int no, MidiRecorder* recorder):
	channelNo_(no),
	programNo_(0),//default acoustic grand piano
	octaveNo_(0),
	midiout_(midi),
    recorder_(recorder)
{
	//set acoustic grand piano as default
	vector<uchar> message(2);
	message[0] = 192 + channelNo_;
	message[1] = programNo_;
  	midiout_->sendMessage(&message);
  	if (recorder_ != NULL)
        //recorder_->write(message, 1);       
    
    
  	for (int i = 0; i < 93; i++)
		controls_[i] = 0;
		
  	// Channel Volume (cc#7), default max volume
  	message[0] = 176 + channelNo_;
	message[1] = 7;
	message.push_back(127);
	midiout_->sendMessage(&message);
	controls_[7] = 127;		
	if (recorder_ != NULL);
       // recorder_->write(message, 1);       
    
}

Channel::~Channel() {
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
       // recorder_->write(message, 1);       
    
}
	 
//Change the instrument.
void Channel::setProgram(uchar program) {
	programNo_ = program;
	vector<uchar> message(2);
	message[0] = 192 + channelNo_;
	message[1] = programNo_;
  	midiout_->sendMessage(&message);

    if (recorder_ != NULL);
        //recorder_->write(message, 1);       
    
}
	
//Plays the given note in default octave.
void Channel::play(uchar note, uchar velocity, int octave) {
	note_[0] = note;
	note_[1] = velocity;
	octaveNo_ = octave;
	vector<uchar> message(3);
  	message[0] = 144 + channelNo_;
  	message[1] = note + octave;
  	message[2] = velocity;
  	midiout_->sendMessage(&message);
    
    if (recorder_ != NULL)
        recorder_->write(message, 1);       
    
}
	
	
//Stops the playing note.
void Channel::release() {
	vector<uchar> message(3);
	message[0] = 128 + channelNo_;
	message[1] = note_[0] + octaveNo_;
  	message[2] = note_[1];
  	midiout_->sendMessage(&message);
    
    if (recorder_ != NULL)
        recorder_->write(message, 1);       
    
}

void Channel::release(uchar pitch) {
    vector<uchar> message(3);
    message[0] = 128 + channelNo_;
    message[1] = pitch + octaveNo_;
    message[2] = note_[1];
    midiout_->sendMessage(&message);
    
    if (recorder_ != NULL)
        recorder_->write(message, 1);       
    
}

  

}
