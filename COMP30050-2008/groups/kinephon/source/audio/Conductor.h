#ifndef CONDUCTOR_H_
#define CONDUCTOR_H_

/**
 * Wrapper class for MidiPlayer, hiding the MIDI particular message 
 * passing and providing a musically oriented interface instead.
 * Good webpages for reference:
 * wikipedia and google :-)
 * http://www.wonderful-music.com/philosophy.html
 * http://www.classicalarchives.com/tutorial/
 * http://www.midistudio.com/Management/R-Finley/MidiTips.html
 * @author      ED
 * @version     1.0
 */

namespace audio
{
//Note:
// The following enumerated types may be extended/shortend/changed/discarded
// depending on whether we will actually use them and how.	
enum Rhythm { RHYTHM_3_4, RHYTHM_4_4, RHYTHM_5_4, RHYTHM_6_4, RHYTHM_7_4,RHYTHM_8_4, RHYTHM_NONE };

// Which notes the chords should be based on.
// Assuming a chord will be composed of 3 notes.
enum Chords { CHORDS_FIRST, CHORDS_SECOND, CHORDS_THIRD, CHORDS_NONE, CHORDS_ONEOFF };

enum Dynamics { DYNAMICS_PIANO, DYNAMICS_FORTE, DYNAMICS_PIANISSIMO, DYNAMICS_FORTISSIMO };

enum Texture { TEXTURE_OMNI, TEXTURE_MONO, TEXTURE_POLY };

class Conductor
{
public:
	/**
    * Constructs a new Conductor class.
    */
	Conductor();
		
	virtual ~Conductor();
	
	/**
	 * Produces a sound based on the settings specified previously.
	 * This class will have to be called in regular intervals to ensure
	 * a consitent timing, e.g. each time it is invoked, it is assumed a 
	 * quarter note has passed. 
	 */
	void play();
	
	/**
	 * Produces a sound based on the settings specified previously as well as the lead melody.
	 * This class will have to be called in regular intervals to ensure
	 * a consitent timing, e.g. each time it is invoked, it is assumed a 
	 * quarter note has passed. 
	 * Only the lead note is specified, the accompaniement and other effects
	 * have been specified before and will be included automatically.
	 * Note that if a melody has been set previously, it will be ignored until play()
	 * is called again.
	 * @param pitch the pitch of the lead  
	 */
	void play(uchar pitch);
	
	
	/**
	 * Plays the lead and accompanying melody together with previously set effects.
	 * This class will have to be called in regular intervals to ensure
	 * a consitent timing, e.g. each time it is invoked, it is assumed a 
	 * quarter note has passed. 
	 * Using this method any previously set accompaniment and melody will be ignored,
	 * however not turned off.
	 * @param pitch the pitch of the lead
	 * @param accompany the pitch of the accompanying melody  
	 */
	void play(uchar pitch, uchar accompany);
	
	/**
	 * Sets the instrument for the lead voice.
	 * @param instrument the instrument to be used
	 */
	void setLeadInstrument(uchar instrument); 
	
	/**
	 * Sets whether a accompaniment is to be played.
	 * The paramenters will specify the nature of the accompaniment. 
	 * @param isOn true if accompaniment is set on
	 * @param paramOne to be decided
	 */
	void setAccompaniment(bool isOn, int paramOne);
	
	/**
	 * Sets whether chords are to be played.
	 * The parameters will specify the nature of the chords. 
	 * @param isOn true if chords are set on
	 * @param chords setting what type of chords to play
	 */
	void setChords(bool isOn, Chords chords);
	
	/**
	 * Sets a basic rhythm.
	 * @param isOn true if rhythm is to be played
	 * @param rhythm selected rhythm 
	 */
	void setRhythm(bool isOn, Rhythm rhythm);
	
	/**
	 * Modifies the basic rhythm.
	 * The parameters will specify the modification.
	 * This function will be used to make the rhythm of the piece more interesting, 
	 * i.e. less monotonous, but ensuring that the changes made will be appropriate.
	 * Rhythm will be automatically set ON, if this has not happened previously.
	 * Note that the definitive structure will be based on further 
	 * development of the project.
	 * @param paramOne to be decided
	 * @param paramTwo to be decided
	 */
	void modifyRhythm(int paramOne, int paramTwo);
	
	/**
	 * Sets the dynamics for the next note.
	 * This setting will be kept until the next call to this function
	 * or until automatic Dynamics are turned on.
	 * @param
	 * @return
	 */
	void setDynamics(Dynamics dynamics);
	
	/**
	 * Sets the class to automatically vary the dynamics.
	 * Some algorithm will vary the dynamics based on the lead melody
	 * played, adding crescendos and diminuendos (gradually getting
	 * louder or quieter) 
	 * @param isOn true if automaticDynamics is to be used
	 */
	void setAutomaticDynamics(bool isOn);
	
	/**
	 * Controls the interaction when two or more notes are played simultaneously.
	 * @param isOn true if interaction is set on, false if it is to be ignored
	 * @param paramOne to be decided
	 */
	void setHarmony(bool isOn, int paramOne);
	
	/**
	 * Plays the given melody repeatedly. 
	 * @param melody vector with pitches, if NULL then this option is set OFF
	 */
	void setMelody(vector<uchar>* melody); 
	
	/**
	 * Sets pedalling on/off.
	 * The frequency will specify after how many played notes the pedal is to be
	 * released. If this method is called in the middle of a pedal-down period
	 * then the pedal will be released and set down again with the new frequency.
	 * @param isOn true is pedaling is to be ON
	 * @param frequency the frequency of pedal-down/pedal-ups
	 */
	void setPedaling(bool isOn, int frequency);
	
	/**
	 * Sets the texture of the piece.
	 * The options are:
	 * Omni mode = all notes sound like played in only one channel
	 * Mono mode = initial note is cut off when a second is played 
	 * Poly mode = plays multiple notes at once (default)
	 */
	void setTexture(Texture texture);
	
	/**
	 * Sets the reverberation on/off.
	 * @param isOn true if reverberation is to be played
	 */
	void setReverberation(bool isOn);
	
private:
	MidiPlayer *midi_;		//midi output
	vector<uchar> melody_;
	bool hasAccompaniment_;
	bool hasChords_;
	bool hasRhythm_;
	bool hasAutoDynamics_;
	bool hasHarmony_;
	bool hasReverb_;
	
	Rhythm rhythm_;
	Chords chords_;
	Dynamics dynamics_;
	Texture texture_;
	
};
}
#endif /*CONDUCTOR_H_*/
