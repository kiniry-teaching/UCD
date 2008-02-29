#ifndef CHANNEL_H_
#define CHANNEL_H_

#include "RtMidi.h"
#include <vector>
using namespace std;
/**
 * Represents a single Midi channel.
 * This class encapsulates the low level, i.e. bit level, details
 * of the Midi messaging mechanism. It also acts as a container for the
 * various settings a Midi channel may have.
 * @author      ED
 * @version		1.0     
 */ 

 namespace audio
{
		
class Channel
{
public:
	/**
	 * Constructs a new channel.
	 * @param midiout reference to Midi output
	 * @param number the number of this channel           
	 */
	Channel(RtMidiOut* midiout, int number);
	
	virtual ~Channel();
	
	/**
	 * Gets the control change value of the specified option.
	 * @param control the control change option we are interested in
	 * @return the program value     
	 */
	unsigned char getControl(unsigned char control);
	

	/**
	 * Gets the program value.
	 * @return the program value     
	 */
	unsigned char getProgram();
	
		
	/**
	 * Sets the given control to specified value.
	 * @param function number of control option
	 * @param value the value of the option      
	 */
	void setControl(unsigned char function, unsigned char value);
	 
	/**
	 * Sets the program, ie instrument on this channel.
	 * @param program the instrument to be         
	 */
	void setProgram(unsigned char program);

  	/**
	 * Sends a Note On message to play a note.
	 * @param note the pitch to be played
	 * @param velocity the velocity with which the note sounds 
	 * @param octave the octave the specified pitch is in     
	 * @return      
	 */
	void Play(unsigned char note, unsigned char velocity, int octave);
	
	/**
	 * Sends a Note Off message.
	 */
	void Release();
	
	
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
		
	
private:
	unsigned char channelNo_;
	unsigned char programNo_;
	unsigned char octaveNo_;
	unsigned char note_[2];			  //note and velocity of last played
	vector<unsigned char> controls_; 
	RtMidiOut* midiout_;
	
	
};
}
#endif /*CHANNEL_H_*/
