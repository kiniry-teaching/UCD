#ifndef CONDUCTOR_H_
#define CONDUCTOR_H_

#include "MidiPlayer.h"

//Note:
// The following enumerated types may be extended/shortend/changed/discarded
// depending on whether we will actually use them and how.	
enum Rhythm { RHYTHM_3_4, RHYTHM_4_4, RHYTHM_5_4, RHYTHM_6_4, RHYTHM_7_4,RHYTHM_8_4, RHYTHM_NONE };

// Which notes the chords should be based on.
// Assuming a chord will be composed of 3 notes.
enum Chords { CHORDS_FIRST, CHORDS_SECOND, CHORDS_THIRD, CHORDS_NONE, CHORDS_ONEOFF };

enum Dynamics { DYNAMICS_PIANO, DYNAMICS_FORTE, DYNAMICS_PIANISSIMO, DYNAMICS_FORTISSIMO };

enum Texture { TEXTURE_OMNI, TEXTURE_MONO, TEXTURE_POLY };

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
class Conductor
{
public:
	/**
    * Constructs a new Conductor class.
    */
	Conductor();
    
    /**
     * Destroy this Conductor.
     */		
	virtual ~Conductor();
	
	/**
	 * Initializes the Conductor.
	 * This will open available Midi ports. 
	 * If this method returns false, all subsequent calls to the other classes
	 * will not have any effect. 
	 * @return true if connection established, false if no connection to a MIDI port
	 */
	bool initialize();
	
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
	 * Plays given note immediately.
	 * This methods caters for notes of a melody played outside
	 * of the normal rhythm. The note will be played with the same
	 * instrument as the usual lead notes.
	 * @param pitch	pitch of the note
	 * @param velocity velocity of the note
	 */
	void playImmediate(uchar pitch, uchar velocity);
	
	/**
	 * Sets the instrument for the lead voice.
	 * <p>
	 * <i> Effect </i>
	 * <ul>
	 * <li> piano (#0 - #7), #0 is the acoustic grand piano
	 * <li> chromatic percussion (#8 - #15)
	 * <li> organ (#16 - #23)
	 * <li> guitar (#24 - #31)
	 * <li> bass (#32 - #39)
	 * <li> strings (#40 - #55)
	 * <li> brass (#56 - #63)
	 * <li> reed (#64 - #71)
	 * <li> pipe (#72 - #79)
	 * <li> synth lead (#80 - #87)
	 * <li> synth pad (#88 - #95)
	 * <li> synth effects (#96 - #103)
	 * <li> ethnic (#104 - #111)
	 * <li> percussive (#112 - #118)
	 * <li> sound effects (#119 - #127)
	 * </ul>
	 * @param instrument the instrument to be used
	 */
	void setLeadInstrument(uchar instrument); 
	
	/**
	 * Sets whether a accompaniment is to be played.
	 * The paramenters will specify the nature of the accompaniment. 
	 * <p>
	 * <i> Effect </i>
	 * The accompaniment is usually at a lower level than the (lead) melody, i.e. at lower volume;
	 * it should not overpower the melody.
	 * To emphisize a given melody in a piece, the accompaniment will play the same notes, 
	 * only at an octave or two lower.
	 * To make the music sound less empty, one would pick up only some of the melody's notes,
	 * e.g. one can play always the third or fourth. For a more interesting piece, these intervals
	 * can be varied.
	 * @param isOn true if accompaniment is set on
	 * @param paramOne to be decided
	 */
	void setAccompaniment(bool isOn, int paramOne);
	
	/**
	 * Sets whether chords are to be played.
	 * The parameters will specify the nature of the chords. 
	 * If chords are to be turned off, the second argument is irrelevant.
	 * <p>
	 * <i> Effect </i>
	 * Chords are three or more notes played together. It provides a more fully sounding
	 * background, whereas simple accompaniment will generally sound more subtle.
	 * This class will use 3 notes and the basis for the chord.
	 * CHORDS_FIRST means that the first note of the chord will be the lead note,
	 * CHORDS_SECOND the second will be the lead note etc.
	 * @param isOn true if chords are set on
	 * @param chords setting what type of chords to play
	 */
	void setChords(bool isOn, Chords chords);
	
	/**
	 * Sets a basic rhythm.
	 * If rhythm is to be turned off, the second argument is irrelevant.
	 * <p>
	 * <i> Effect </i>
	 * This effect can be compared to beats in, say, a popsong.
	 * Lead, accompanying and chord notes can be played at random time intervals,
	 * whereas rhythm will always stay the same throughout the music piece, 
	 * thus adding some structure.
	 * However, for very subtle melodies this feature might not be suitable as it might
	 * feel too forceful. 
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
	 * This setting will affect both the lead and the accompaniment(if it is turned on),
	 * maintaining their relative volumes, i.e. lead will be always louder.
	 * <p>
	 * <i> Effect </i>
	 * This effect can be described as softness or loudness of the music.
	 * It can be used e.g. to emphasize some notes of the melody.
	 * <ul>
	 * <li> piano (soft)
	 * <li> forte (loud, strong)
	 * <li> pianissimo (very quiet)
	 * <li> fortissimo (very strong)
	 * </ul>
	 * @param dynamics the type of dynamics to use
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
	 * If harmony is to be turned off, the second argument is irrelevant.
	 * <p>
	 * <i> Effect </i>
	 * Harmony has an abiguous meaning in music, 
	 * it may mean the (perfect) intervals between two pitches, so as to make them sound 'nice' or consonant
	 * or the whole structure of the piece (only consonant notes will sound very boring).
	 * The exact behaviour of this method is dependent on future development. 
	 * @param isOn true if interaction is set on, false if it is to be ignored
	 * @param paramOne to be decided
	 */
	void setHarmony(bool isOn, int paramOne);
	
	/**
	 * Plays the given melody repeatedly. 
	 * The format of the vector data is to be as follows:
	 * each note consists of a pitch and a velocity value
	 * e.g.: 60, 60, 61, 127, 60, 60
	 * will play 3 notes, of which the middle one is 'more forceful' and one note higher.
	 * The passed vector has to have an EVEN size.
	 * This format my change later to allow for more complicated melodies. 
	 * @param melody vector with pitches, if NULL then this option is set OFF
	 */
	void setMelody(vector<uchar> melody); 
	
	/**
	 * Sets pedalling on/off.
	 * The frequency will specify after how many played notes the pedal is to be
	 * released. If this method is called in the middle of a pedal-down period
	 * then the pedal will be released and set down again with the new frequency.
	 * <p>
	 * <i> Effect </i>
	 * Pedaling blends notes together, making the music sounding more 'together'.
	 * If some notes are to be emphasized, however, pedalling might be inappropriate.
	 * @param isOn true is pedaling is to be ON
	 * @param frequency the frequency of pedal-down/pedal-ups
	 */
	void setPedaling(bool isOn, int frequency);
	
	/**
	 * Sets the texture of the piece.
	 * <p>
	 * <i> Effect </i>
	 * This effect will affect the overall sound of the piece.
	 * <ul>
	 * <li> Omni mode  (all notes sound like played in only one channel)
	 * <li> Mono mode  (initial note is cut off when a second is played) 
	 * <li> Poly mode  (plays multiple notes at once) (default)
	 * </ul>
	 * @param texture texture to be used
	 */
	void setTexture(Texture texture);
	
	/**
	 * Sets the reverberation on/off.
	 * <p>
	 * <i> Effect </i>
	 * 
	 * @param isOn true if reverberation is to be played
	 */
	void setReverberation(bool isOn);
	
	/**
	 * Releases all notes.
	 * Additional functionality, like restoring default state, may be added
	 * if need arises.
	 */
	void pressPanicButton();
	
private:
	MidiPlayer *midi_;		//midi output
	int timeStep_;
	int melodyStep_;
	
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
#endif /*CONDUCTOR_H_*/
