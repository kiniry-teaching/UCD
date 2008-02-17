#ifndef CHANNEL_H_
#define CHANNEL_H_

#include "RtMidi.h"

/*
 * Author:	ED
 *
 * Represents one channel of sound with its individual settings.
 *
 */

class Channel
{
public:
	//Open a new channel
	//TODO: what's the default program??
	Channel(RtMidiOut *midiout, int no);
	//TODO: is there anything to destroy here??
	virtual ~Channel();

	//program settings, program = "instrument"
	char getProgram();
	void setProgram(char prog);
		
	//send a message to RtMidiOut	
	void play();
	
	//don't know yet what it does, but it's useful
	void pitchBend();
	
private:
	int number;
	char program;
	
};

#endif /*CHANNEL_H_*/
