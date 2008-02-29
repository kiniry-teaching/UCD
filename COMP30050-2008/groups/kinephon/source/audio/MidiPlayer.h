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

namespace audio
{
/**
 * General Midi player.
 * This class provides facilities to connect to available Midi ports and to
 * play audio based on several dedicated channels, such as rhythm, chords and percussion.
 * This class provides a middle level of abstraction, so it is kept intentionally
 * technical. It is intended not to obscure the details of the Midi messaging mechanism.  
 * @author ED
 * @version  1.0
 */
class MidiPlayer
{
public:
	/**
	 * Creates a new MidiPlayer that is not yet connected to any port.
	 * <code>initialize()</code> has to be called to enable playback.       
	 */
	MidiPlayer();
	
	virtual ~MidiPlayer();
	
	/**
	 * Attempts to connect to an available MIDI port.
	 * If more than one port is available, then a choice is given.       
	 * @return true if connection has been established, false if an error occured     
	 */
	bool initialize();
	
	/**
	 * Sends a Universal System Exclusive Message.
	 * They control Master volume, reverb, chorus and others. 
	 * Only necessary options will be made available.
	 * @param message type of function
	 * @param value value of specified function      
	 */
	void sendSysEx(int message, int value);
	
	
	/**
	 * Sends a Channel Mode message affecting all channels.
	 * The following options are available: 
	 * #121 Local Control  Off
	 * #122 Local Control On
	 * #123 All Notes Off
	 * #124 Omni Mode Off
	 * #125 Omni Mode ON
	 * #126 Mono mode On
	 * #127 Poly Mode On
	 * @param mode messageto be sent      
	 */
	void sendChannelMode(unsigned char mode );
	
	/**
	 * Sends a Control Change message to one channel.
	 * According to General MIDI 2 specification there are the following options:
	 * Bank Select (cc#0/32)
     * Modulation Depth (cc#1)
     * Portamento Time (cc#5)
     * Channel Volume (cc#7)
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
	 * Note: which of these will actually be implemented is yet to be decided.
	 * @param channel the channel the message is to be sent to      
	 * @param function the chosen function 
	 * @param value the value of the function
	 */
	void sendControlChange(unsigned char channel, unsigned char function, unsigned char value);
	
	/**
	 * Sends a Program Change message to one channel.
	 * According to MIDI standard there are 127 different options, which can be grouped 
	 * as follows:
	 * ~ piano
	 * ~ chromatic percussion
	 * ~ organ
	 * ~ guitar
	 * ~ bass
	 * ~ strings
	 * ~ brass
	 * ~ reed
	 * ~ pipe
	 * ~ synth lead
	 * ~ synth pad
	 * ~ synth effects
	 * ~ ethnic 
	 * ~ percussive
	 * ~ sound effects
	 * * Note: which of these will actually be used is yet to be decided.
	 * @param channel the channel the message is to be sent to       
	 * @param program selected instrument number
	 */
	void sendProgramChange(unsigned char channel, unsigned char program);
	
  	/**
	 * Plays a note of given pitch on given channel.
	 * The pitch value will be interpreted differently for different channels.
	 * @param channel the channel to be used
	 * @param pitch the value of the note to be played            
	 */
	void playNote(Channels channel, unsigned char pitch);
	
  	
  	/**
	 * Plays a note of given pitch and velocity on given channel.
	 * The pitch and velocity value will be interpreted differently for different channels.
	 * @param channel the chnnel to be used
	 * @param pitch the value of the note to be played
	 * @param velocity the velocity of the note
	 */
	void playNote(Channels channel, unsigned char pitch, unsigned char velocity);
	
	/**
	 * Additional methods may be included if need arises.
	 */
	void otherOptions();
	
	enum Channels {CHANNEL_LEAD, CHANNEL_ACCOMPANY, CHANNEL_PERCUSSION, CHANNEL_CHORD};
	
private:
	RtMidiOut* _midiout;
	vector<Channel> _channels;	
	bool isConnected_;
	Channel* defaultChannel_;
	Channel* chordChannel_;
	Channel* accompanyChannel_;
	Channel* percussionChannel_; //channel 10
};
}
#endif /*MIDIPLAYER_H_*/
