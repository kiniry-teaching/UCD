#ifndef CHANNEL_H_
#define CHANNEL_H_

#include "RtMidi.h"
#include <vector>
using namespace std;
/*
 * Author:	ED
 *
 * Represents one channel of sound with its individual settings.
 *
 */
	/* 
	 * Define middle notes as constants, these are essential.
	 * What octave we are in is less important for the tune. 
	 */
	const unsigned char MIDDLE_C = 60;
	const unsigned char MIDDLE_CSHARP = 61;
	const unsigned char MIDDLE_D = 62;
	const unsigned char MIDDLE_DSHARP = 63;
	const unsigned char MIDDLE_E = 64;
	const unsigned char MIDDLE_F = 65;
	const unsigned char MIDDLE_FSHARP = 66;
	const unsigned char MIDDLE_G = 67;
	const unsigned char MIDDLE_GSHARP = 68;
	const unsigned char MIDDLE_A = 69;
	const unsigned char MIDDLE_ASHARP = 70;
	const unsigned char MIDDLE_B = 71;
	
	/*
	 * To be extended depending on functions needed.
	 * Maybe we need those as constants as well, for efficient indexing in array.
	 */
	enum Control {
		VOLUME,
		PORTAMENTO
	};
class Channel
{
public:
	//Open a new channel
	//TODO: what's the default program??
	Channel(RtMidiOut *midi, int no);
	//TODO: is there anything to destroy here??
	virtual ~Channel();

public://Properties
	
	/* 
	 * Returns the mode of the specified function. 
	 */
	unsigned char ControlChange(unsigned char channel);
	
public://Methods
		
	/* 
	 * Adjusts this channel's settings 
	 */
	void ControlChange(unsigned char function, unsigned char value);
	 
	/*
	 *	Change the instrument.
	 */
	void ProgramChange(unsigned char program);
	
  	/* 
  	 * Plays the given note in default octave.
  	 */
	void Play(unsigned char note, unsigned char velocity);
	
	/* 
  	 * Plays the given note in specified octave.
  	 */
	void Play(unsigned char note, unsigned char velocity, int octave);
	
	/* 
  	 * Plays the given chord in specified octave.
  	 */
	void PlayChord(unsigned char chord, unsigned char velocity, int octave);
	
	/* 
  	 * Stops the playing note.
  	 */
	void Release(unsigned char note, unsigned char velocity);
	
		
	
private:
	unsigned char _number;
	unsigned char _program;
	unsigned char _octave;
	RtMidiOut *_midiout;
	//unsigned char _controlChange[1][1];
	/*TODO*/
	//const unsigned char _chordMatrix[0][0];
	
};

#endif /*CHANNEL_H_*/
