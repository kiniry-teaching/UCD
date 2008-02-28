#ifndef CONDUCTOR_H_
#define CONDUCTOR_H_

/*
 * Author:	ED
 *
 * Wrapper class for MidiPlayer, hiding the MIDI particular message 
 * passing and providing a musically oriented interface instead.
 * 
 */

//Note:
// The following enumerated types may be extended/shortend/changed/discarded
// depending on whether we will actually use them and how.
// This should just us an idea.

enum Rhythm { RHYTHM_3_4, RHYTHM_4_4, RHYTHM_5_4, RHYTHM_6_4, RHYTHM_7_4,RHYTHM_8_4, RHYTHM_NONE };

// Which notes the chords should be based on.
// Assuming a chord will be composed of 3 notes.
enum Chords { CHORDS_FIRST, CHORDS_SECOND, CHORDS_THIRD, CHORDS_NONE };

enum Dynamics { DYNAMICS_PIANO, DYNAMICS_FORTE, DYNAMICS_PIANISSIMO, DYNAMICS_FORTISSIMO };

enum Texture { TEXTURE_MONOPHONIC, TEXTURE_POLYPHONIC };

class Conductor
{
public:
	/**
    * Constructs a new Conductor class.
    */
	Conductor();
	/**
    * Deletes all dynamic datastructures needed
    */	
	virtual ~Conductor();
	
	/**
	 * Plays, i.e. produces a sound based on the settings specified
	 * below.
	 * This class will have to be called in regular intervals to ensure
	 * a consitent timing. 
	 */
	void play();
	
	
	/**
	 * This will change the piece from one key to another, basically
	 * by changing the pitches specified in the melody buffer.
	 * Optionally, the changes might affect future notes as well.
	 */
	void changeModulation(unsigned char key); 
	
	/**
	 * Plays the given melody, i.e. the pitches specified in the vector. 
	 * If vector has 1 element play note immediately.
	 * If vector has more elements, place into buffer.
	 */
	void setMelody(vector<unsigned char> melody); 
	 	
	/**
	 * Based on the Rhythm specified, a rhythm pattern will be set up
	 * of different instruments like drums, bass, piano etc.  
	 */
	void setRhythm(Rhythm rhythm); 
	 
	/**
	 * Set whether and chords are to be played.
	 * Frequency of 1 will play a chord with each note,
	 * freq. of 3 will play one with every third one.
	 */ 
	void setChords(Chords mode, unsigned char frequency);
	
	/**
	 * This sets the number of voices in the music piece, and also 
	 * in some cases whether any accompaniment is present.
	 */
	void setTexture(Texture texture);
	 	
	/**
	 * This will analyze the melody saved in the buffer and correct
	 * the intonation of the piece to a more harmonic sounding.
	 * This feature can be turned on or off, or can be specified how much
	 * this should occur. 
	 * (E.g. 10 will specify, ONE note in 10 will be corrected at max.)
	 */
	void correctHarmony(bool on, unsigned char amount);
	 	
	/**
	 * This will create some dissonance in the piece. 
	 * (To be determined how, options are in chords, in )
	 */
	void createDissonance(unsigned char amount); 	
	 
	
	
private:
	MidiPlayer *midi_;		//midi output
	unsigned char key_;		//key of this piece
	vector<unsigned char> buffer_;
	Rhythm rhythm_;
	Chords chords_;
	Dynamics dynamics_;
	Texture texture_;
	//Optional, if need arises. Advanced music
	vector<bool> keySignature_; 	//determines which notes are played "sharp"
	
};

#endif /*CONDUCTOR_H_*/