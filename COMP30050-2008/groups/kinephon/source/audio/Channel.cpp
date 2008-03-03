#include "Channel.h"

Channel::Channel(RtMidiOut* midi, int no):
	channelNo_(no),
	programNo_(0),
	octaveNo_(0),
	midiout_(midi)
{
	//set acoustic grand piano as default
	vector<uchar> message(2);
	message[0] = 192 + channelNo_;
	message[1] = programNo_;
  	midiout_->sendMessage(&message);
  	
  	for (int i = 0; i < 93; i++)
		controls_[i] = 0;
		
  	// Channel Volume (cc#7), default max volume
  	message[0] = 176 + channelNo_;
	message[1] = 7;
	message.push_back(127);
	midiout_->sendMessage(&message);
	controls_[7] = 127;		
	
	//TODO test and set default values
	/** Bank Select (cc#0/32)
     * Modulation Depth (cc#1)
     * Portamento Time (cc#5)
     
     * Pan (cc#10)
     * Expression (cc#11)
     * Hold1 (Damper) (cc#64)
     * Portamento ON/OFF (cc#65)
     * Sostenuto (cc#66)
     * Soft (cc#67)
     * Filter Resonance (Timbre/Harmonic Intensity) (cc#71)
     * Release Time (cc#72)
     * Brightness (cc#74)
     * Decay Time (cc#75) (new message)
     * Vibrato Rate (cc#76) (new message)
     * Vibrato Depth (cc#77) (new message)
     * Vibrato Delay (cc#78) (new message)
     * Reverb Send Level (cc#91)
     * Chorus Send Level (cc#93)
     * Data Entry (cc#6/38)
     * RPN LSB/MSB (cc#100/101)
     */
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
}
	 
//Change the instrument.
void Channel::setProgram(uchar program) {
	programNo_ = program;
	vector<uchar> message(2);
	message[0] = 192 + channelNo_;
	message[1] = programNo_;
  	midiout_->sendMessage(&message);
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
}
	
	
//Stops the playing note.
void Channel::release() {
	vector<uchar> message(3);
	message[0] = 128 + channelNo_;
	message[1] = note_[0] + octaveNo_;
  	message[2] = note_[1];
  	midiout_->sendMessage(&message);
}

void Channel::release(uchar pitch) {
    vector<uchar> message(3);
    message[0] = 128 + channelNo_;
    message[1] = pitch + octaveNo_;
    message[2] = note_[1];
    midiout_->sendMessage(&message);
}

