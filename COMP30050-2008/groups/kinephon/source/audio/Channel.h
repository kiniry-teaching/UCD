#ifndef CHANNEL_H_
#define CHANNEL_H_

#include "RtMidi.h"
#include "MidiRecorder.h"
#include "../type.h"
#include <vector>
using namespace std;

namespace audio
{ 
	/* 
	 * Define notes as constants, these are essential.
	 * What octave we are in is less important for the tune. 
	 */
	const uchar NOTE_C = 12;
	const uchar NOTE_CSHARP = 13;
	const uchar NOTE_D = 14;
	const uchar NOTE_DSHARP = 15;
	const uchar NOTE_E = 16;
	const uchar NOTE_F = 17;
	const uchar NOTE_FSHARP = 18;
	const uchar NOTE_G = 19;
	const uchar NOTE_GSHARP = 20;
	const uchar NOTE_A = 21;
	const uchar NOTE_ASHARP = 22;
	const uchar NOTE_B = 23;

/**
 * Represents a single Midi channel.
 * This class encapsulates the low level, i.e. bit level, details
 * of the Midi messaging mechanism. It also acts as a container for the
 * various settings a Midi channel may have.
 * @author      ED
 * @version     1.0     
 */ 		
class Channel
{
public:
	/**
	 * Constructs a new channel.
	 * @param midiout reference to Midi output
	 * @param number the number of this channel   
	 * @throws RtError if anything went wrong          
	 */
	Channel(RtMidiOut* midiout, int number, MidiRecorder* recorder);
	
    /**
     * Destroy this Channel.
     */
	virtual ~Channel();
	
	/**
	 * Gets the control change value of the specified option.
	 * @param control the control change option we are interested in
	 * @return the program value     
	 */
	uchar getControl(uchar control);
	

	/**
	 * Gets the program value.
	 * @return the program value     
	 */
	uchar getProgram();
	
		
	/**
	 * Sets the given control to specified value.
	 * @param function number of control option
	 * @param value the value of the option      
	 * @throws RtError if anything went wrong
	 */
	void setControl(uchar function, uchar value);
	 
	/**
	 * Sets the program, ie instrument on this channel.
	 * @param program the instrument to be   
	 * @throws RtError if anything went wrong      
	 */
	void setProgram(uchar program);

  	/**
	 * Sends a Note On message to play a note.
	 * @param pitch the pitch to be played
	 * @param velocity the velocity with which the note sounds
     * @param deltaTime delay to be used when writing the MIDI file      
	 * @throws RtError if anything went wrong       
	 */
	void play(uchar pitch, uchar velocity, ulong deltaTime);
	
	/**
	 * Sends a Note Off message for the last played pitch.
     * @param deltaTime delay to be used when writing the MIDI file
	 * @throws RtError if anything went wrong  
	 */
	void release(ulong deltaTime);
	
	/**
     * Sends a Note Off message for a specific pitch.
     * This method is necessary to cater for chords, since we have 3 simultaneous
     * pitches there.
     * @param pitch the pitch of the note to be released
     * @param deltaTime delay to be used when writing the MIDI file
     * @throws RtError if anything went wrong  
     */
    void release(uchar pitch, ulong deltaTime);
		
	
private:
	uchar channelNo_;
	uchar programNo_;
	uchar note_[2];			  //note and velocity of last played
	uchar controls_[93]; 
	RtMidiOut* midiout_;
	MidiRecorder* recorder_;
	
};
}
#endif /*CHANNEL_H_*/
