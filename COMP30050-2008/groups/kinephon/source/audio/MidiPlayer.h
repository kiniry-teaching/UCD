#ifndef MIDIPLAYER_H_
#define MIDIPLAYER_H_

#include "Channel.h"
#include "RtMidi.h"
#include <string>
using namespace std;

#if defined(__WINDOWS_MM__)
  #include <windows.h>
  #define SLEEP( milliseconds ) Sleep( (DWORD) milliseconds ) 
#else // Unix variants
  #include <unistd.h>
  #define SLEEP( milliseconds ) usleep( (unsigned long) (milliseconds * 1000.0) )
#endif

/*
 * Author:	ED
 *
 * Interface for audio creation that is in charge of all audio
 * operations.
 * 
 */
/*TODO TODO TODO TODO: EXHAUSTIVE TESTING FOR EXCEPTIONS*/

class MidiPlayer
{
public://Constructor
	/* Creates a new MidiPlayer which is NOT yet connected to a port */
	MidiPlayer();
	
	/* deletes RtMidiOut class */
	virtual ~MidiPlayer();
	/* 
	 * Returns false, if connection to a port has not been established.
	 */
	bool init();

public://Properties
	/* Returns the channels mode */
	unsigned char ChannelMode();

	/* Returns the mode of the specified channel */
	unsigned char ControlChange(unsigned char channel);
	
public://Methods for manually sending messages (if necessary, some may be made private)
	
	/* 
	 * Open a new channel (maybe return it's number)
	 * This will set up the necessary settings (to default values).
	 * @returns the number of the newly opened channel
	 */
	int openChannel();

	/* Adjusts channel mode */
	void setChannelMode(unsigned char mode );
	
	/* Adjusts each channel's setting separately */
	void changeControl(unsigned char channel, unsigned char function, unsigned char value);
	
	/*
	 *	Change the instrument on given channel.
	 */
	void setProgram(unsigned char channel, unsigned char program);
	
	/* Turns all notes off (maybe if necessary later, it will also close all channels) */
	void panic();
  	
  	/*
  	 * Based on nature of event an effect is set on one/several/all channels.
  	 * Events to be decided. 
  	 */
  	void Event(string event);
  	
  	/*
  	 * Sets the default velocity on all channels.
  	 */
  	void setVelocity(unsigned char velocity);
  	
  	/*
  	 * Plays a chord on the chord channel.
  	 */
  	void playChord();
  	
  	/* 
  	 * Plays or stops the given note on given channel with 
  	 * preset velocity.
  	 */
	void playNote(bool on, unsigned char pitch);
	
  	
  	/* 
  	 * Plays or stops the given note on given channel with
  	 * specific velocity.
  	 */
	void playNote(bool on, unsigned char pitch, unsigned char velocity);
	
	/* 
  	 * Plays or stops the given note on the rhythm channel.
  	 * TODO: this doesnt work yet, needs a bit of research.
  	 */
	void playRhythm(bool on, unsigned char pitch, unsigned char velocity);
	
	/*
	 * And more funtions to be added depending on the input format from the interpreter class.
	 * Maybe more internal analysis will be need. 
	 * E.g. the interpreter could supply information like acceleration, velocity, position,
	 * special defined gestures etc etc.
	 * This function will be overloaded for consistency.
	 */
	void Input(int tune);
	
	
	/*
	 * various other features can be added depending on need arising.
	 */
	void pause();
	
private:
	RtMidiOut *_midiout;
	vector<Channel> _channels;	
	vector<unsigned char> _playing_notes;
	bool _connected;
	Channel *_defaultChannel;
	Channel *_rhythmChannel;
	Channel *_chordChannel;
};

#endif /*MIDIPLAYER_H_*/
