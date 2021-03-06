#ifndef CONDUCTOR_H_
#define CONDUCTOR_H_

#include "MidiPlayer.h"

namespace audio {
    
/** 
 * What kind of rhythm should be used. The numbers should be read as 1_4 = 1/4, i.e. play one beat every 4 time steps.
 */
enum Rhythm { RHYTHM_1_4, RHYTHM_2_4, RHYTHM_3_4, RHYTHM_4_4, RHYTHM_1_2, RHYTHM_2_3, RHYTHM_NONE };

/** 
 * Which notes the chords should be based on. 
 * Assuming a chord will be composed of 3 notes. All chords are based on the note played on the first beat.
 * The first three options play 3 notes simultaneously and hold it, the CHORDS_123 builds the chord gradually.
 * The difference between the first three options is which note in the chord the note played on first beat is.
 * Note that if the note on first beat is NO_NOTE, the last first beat note will be used for chords.
 * 
 */
enum Chords { CHORDS_FIRST, CHORDS_SECOND, CHORDS_THIRD, CHORDS_123, CHORDS_NONE };

/** 
 * What dynamics should be used, i.e. loud (forte) or quiet(piano).
 */
enum Dynamics { DYNAMICS_PIANO, DYNAMICS_FORTE, DYNAMICS_PIANISSIMO, DYNAMICS_FORTISSIMO };

/**
 * These instruments set suitable combinations of instruments for lead and chords.
 * Can be easily extended.  
 */
enum Instrument { INSTRUMENT_CLASSIC, INSTRUMENT_CRAZY, INSTRUMENT_WIND };
/**
 * No note, i.e. temporary pause signal.
 */
const uchar NO_NOTE = 255;


/**
 * Wrapper class for MidiPlayer, hiding the MIDI particular message passing and providing a musically oriented interface instead.
 * It is supposed to be an independent application, hence functions may be included not needed for the project Kinephon.
 * Good webpages for musical theory reference:
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
    * @param recording true if the music should be recorded to a MIDI file
    * @param portName name of port to be used (varies depending on synthesizer)     
	 * @return true if connection established, false if no connection to a MIDI port
	 */
	bool initialize(bool recording, string portName);
	
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
    * If no lead note should be played, but the other effects none the less, (e.g. if the last
    * note should be longer) then pitch is to be set to the value NO_NOTE (255). pitchVelocity is not used then.
    * <p>
    * Note: the use of unsigned characters ensures that the specified notes have the correct range. 
    * Also note: If you want to use the absolute pitches, i.e. values ranging 0-127, you can do so,
    * but you have to specify the octave number as 0.
	 * @param note the note of the lead 
    * @param octave play the note in this octave
    * @param pitchVelocity attack velocity of note
	 */
	void play(uchar note, int octave, uchar pitchVelocity);
	
	
	/**
	 * Plays the lead and accompanying melody together with previously set effects.
	 * This class will have to be called in regular intervals to ensure
	 * a consitent timing, e.g. each time it is invoked, it is assumed a 
	 * quarter note has passed. 
	 * Using this method any previously set accompaniment and melody will be ignored,
	 * however not turned off.
    * If no lead note should be played, but the other effects none the less, (e.g. if the last
    * note should be longer) then pitch is to be set to the value NO_NOTE (255). pitchVelocity is not used then. 
    * <p>
    * Note: the use of unsigned characters ensures that the specified notes have the correct range. 
    * Also note: If you want to use the absolute pitches, i.e. values ranging 0-127, you can do so,
    * but you have to specify the octave number such that the pitches will still be in the range of
    * 0-127. Otherwise the output will be unpredictable (the wrong notes will either be played, if valid,
    * or ignored, if you run out of range).
    * The octave parameter can also be used to lower/increase the octaves.
	 * @param note the note of the lead
    * @param octave play the note in this octave
    * @param pitchVelocity attack velocity of note
	 * @param accompany the pitch of the accompanying melody
    * @param accOctave play the accompaniment in this octave  
    * @param accompanyVelocity attack velocity of accompaniment note
	 */
	void play(uchar note, int octave, uchar pitchVelocity, uchar accNote, int accOctave, uchar accVelocity);
	
	/**
	 * Plays given note immediately.
	 * This methods caters for notes of a melody played outside
	 * of the normal rhythm. The note will be played with the same
	 * instrument as the usual lead notes.
    * <p>
    * Note: the use of unsigned characters ensures that the specified notes have the correct range. 
    * Also note: If you want to use the absolute pitches, i.e. values ranging 0-127, you can do so,
    * but you have to specify the octave number such that the pitches will still be in the range of
    * 0-127. Otherwise the output will be unpredictable (the wrong notes will either be played, if valid,
    * or ignored, if you run out of range).
    * The octave parameter can also be used to lower/increase the octaves.
    * @param note pitch of the note
    * @param octave play the note in this octave
	 * @param velocity velocity of the note
    * @param deltaTime time difference when this note should be played
	 */
	void playImmediate(uchar note, int octave, uchar velocity, ulong deltaTime);
	
    /**
     * Returns the currently set instruments.
     * @return the instrument currently set
     */
    Instrument getInstrument();
    
    /**
     * Returns whether accompaniment is turned on.
     * @return true if accompaniment is set
     */
    bool getAccompaniment();
    
    /**
     * Returns the currently set chords. 
     * If no chords are set, the return value will be CHORDS_NONE.
     * @return the currently set chords
     */
    Chords getChords();
     
     /**
     * Returns the currently set rhythm. 
     * If no rhythm is set, the return value will be RHYTHM_NONE.
     * @return the currently set rhythm
     */
    Rhythm getRhythm();
     
     /**
     * Returns the currently set dynamics. 
     * @return the currently set dynamics
     */
    Dynamics getDynamics();
    
      /**
     * Returns the currently set melody.
     * If no melody set, returns empty vector.
     * @return vector with melody notes
     */
    vector<uchar> getMelody();
    
    /**
     * Returns whether pedaling is currently enabled.
     * @return true if pedaling is on
     */
    bool getPedaling();
    
    /**
     * Returns whether reverberation is currently enabled.
     * @return true if reverb is on
     */
    bool getReverberation();
    
    /**
     * Returns the modulation value.
     * A value of 0 means modulation is OFF.
     * @return true if reverb is on
     */
    uchar getModulation();
     
	/**
	 * Sets the instrument for the lead voice.
	 * <p>
	 * <i> Effect </i>
	 * Since the instruments have idividual characteristics, some go better together than others, i.e.
    * in some combinations, one instrument would overpower the others. For this, we will have preset
    * combinations (see the enum type Instrument). 
    * <ul>
    * <li>CLASSIC: lead-acoustic grand piano, chords-string ensemble, rhythm-synth drum
    * <li>CRAZY: lead-woodblock, chords-seashore, rhythm-breath noise  
    * </ul> 
	 * @param instrument the instrument to be used
	 */
	void setInstrument(Instrument instrument); 
	
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
	 */
	void setAccompaniment(bool isOn);
	
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
	 * Plays the given melody repeatedly. 
	 * The format of the vector data is to be as follows:
	 * each note consists of a pitch and a velocity value
	 * e.g.: 60, 60, 61, 127, 60, 60
	 * will play 3 notes, of which the middle one is 'more forceful' and one note higher.
	 * The passed vector has to have an EVEN size.
	 * This format my change later to allow for more complicated melodies. 
	 * @param melody vector with pitches, if the vector has length zero then this option is set OFF
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
    * Also, pedaling will only affect the lead and the accompaniment, since it would be rather 
    * contraproductive for the chords or rhythm.
    * Note: Only frequencies above 8 will have an audible effect. Also the effect is subtle, so in
    * combination with chords and rhythm it may not be noticable any more.
	 * @param isOn true is pedaling is to be ON
	 * @param frequency the frequency of pedal-down/pedal-ups
	 */
	void setPedaling(bool isOn, int frequency);
	
	/**
	 * Sets the reverberation on/off.
	 * <p>
	 * <i> Effect </i>
	 * Has a very small effect, best to be used with no chords/rhythm.
	 * @param isOn true if reverberation is to be played
	 */
	void setReverberation(bool isOn);
	
    /**
     * Sets the modulation wheel.
     * The values range from 0 - 127. O means modulation OFF.
     * Note, if the value is out of this range, nothing will happen, also no crash, except
     * a parsing error will be printed to std::out.
     * <p>
     * <i> Effect </i>
     * Distorts the sound. Hard to describe, so better try it. It sounds funny.
     * @param position the position of the modulation wheel
     */
    void setModulation(uchar position);
        
    void setPan(uchar position);
	/**
	 * Releases all notes.
	 * Additional functionality, like restoring default state, may be added
	 * if need arises.
	 */
	void pressPanicButton();
	
private:
	MidiPlayer *midi_;		       //midi output
    int noNoteCount_;           //needed for correct timing of recorder
	int timeStep_;                    //needed for correct timing  
	int melodyStep_;              //needed for correct timing of the melody vector 
    int melodyLength_;         //save length for safety check, if vector has invalid format
    int pedalingFreq_;     
    int pedalingCounter_;
	
	vector<uchar> melody_; 
	bool hasAccompaniment_;
	bool hasChords_;
	bool hasRhythm_;
    bool hasMelody_;
    bool hasPedaling_;
	bool hasReverb_;
	
   uchar modulation_;    
	Rhythm rhythm_;
	Chords chords_;
   uchar currentChord_;
	Dynamics dynamics_;
   Instrument instrument_;
};
}//end namespace

#endif /*CONDUCTOR_H_*/
