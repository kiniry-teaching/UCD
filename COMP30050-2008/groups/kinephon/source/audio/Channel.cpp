/*#include "Channel.h"

Channel::Channel(RtMidiOut* midi, int no):
	_number(no),
	_program(1),
	_octave(0),
	_midiout(midi)
{
	vector<unsigned char> message(2);
	message[0] = 192 + _number;
	message[1] = _program;
  	_midiout->sendMessage( &message );
  	
  	message[0] = 176 + _number;
	message[1] = 7;
	message.push_back(30);
	_midiout->sendMessage( &message );
  	
}

Channel::~Channel()
{
}

// Returns the mode of the specified function. 
unsigned char Channel::ControlChange(unsigned char channel){
	return 0u;
}
	
//Adjusts this channel's settings 
void Channel::ControlChange(unsigned char function, unsigned char value){}
	 
//Change the instrument.
void Channel::ProgramChange(unsigned char program){}
	
//Plays the given note in default octave.
void Channel::Play(unsigned char note, unsigned char velocity){
	vector<unsigned char> message(3);
  	message[0] = 144 + _number;
  	message[1] = note;
  	message[2] = velocity;
  	_midiout->sendMessage( &message );
	
}
	
//Plays the given note in specified octave.
void Channel::Play(unsigned char note, unsigned char velocity, int octave){}
	
//Plays the given chord in specified octave.
void Channel::PlayChord(unsigned char chord, unsigned char velocity, int octave){}
	
//Stops the playing note.
void Channel::Release(unsigned char note, unsigned char velocity){
	vector<unsigned char> message(3);
	message[0] = 128 + _number;
	message[1] = note;
  	message[2] = velocity;
  	_midiout->sendMessage( &message );
	

}

*/