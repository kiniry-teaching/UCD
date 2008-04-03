#include "Conductor.h"
namespace audio
{
//TODO: getter functions
Conductor::Conductor():
	midi_(NULL),
	timeStep_(0),
	melodyStep_(0),
    melodyLength_(0),
    pedalingFreq_(0),
    pedalingCounter_(0),
	hasAccompaniment_(false),
	hasChords_(false),
	hasRhythm_(false),
	hasAutoDynamics_(false),
	hasHarmony_(false),
    hasMelody_(false),
    hasPedaling_(false),
	hasReverb_(false),
    modulation_(0),//default value to NO modulation
    accompaniment_(0),
    harmony_(0),
    
	rhythm_(RHYTHM_NONE),
	chords_(CHORDS_NONE),
	dynamics_(DYNAMICS_FORTE)
    
{}

Conductor::~Conductor() {
    setModulation(0); //just in case reset this, or it will be remembered
	delete midi_;
}

bool Conductor::initialize(bool recording) {
	midi_ = new MidiPlayer();
	if (!midi_->initialize(recording))
    	return false;
    else {
        setInstrument(INSTRUMENT_CLASSIC);
        setDynamics(DYNAMICS_FORTE);
        setModulation(0); //just in case someone forgot to switch it off last time
    	return true;//now we have 4 channels to play on
    } 
}

//expects 1/4 note steps
void Conductor::play() {
	if (timeStep_ == 0) {//1st quarter 
        if (hasMelody_) {// if no melody, no accompaniment/chords, only rhythm can be played
            uchar pitch = melody_[melodyStep_];
            uchar pitchVelocity = melody_[melodyStep_];
            melodyStep_ = (melodyStep_ + 2) % melodyLength_;
            if (pitch != NO_NOTE) {
                if (hasAccompaniment_) {
                    midi_->releaseChannel(CHANNEL_ACCOMPANY);
                    midi_->playAccompaniment(pitch-12, pitchVelocity); 
                }
                if (hasChords_) {
                    midi_->releaseChannel(CHANNEL_CHORD);
                    midi_->sendControlChange(CHANNEL_CHORD, 64, 0); //turn hold OFF
                    midi_->playChord(pitch-12,10);
                    midi_->sendControlChange(CHANNEL_CHORD, 64, 127); //turn hold ON
                }
                midi_->releaseChannel(CHANNEL_LEAD);
                midi_->playLead(pitch, pitchVelocity);
            }
            
        }
        if (hasRhythm_) {//RHYTHM_1_4, RHYTHM_2_4, RHYTHM_3_4, RHYTHM_4_4, RHYTHM_1_2, RHYTHM_2_3
            midi_->releaseChannel(CHANNEL_PERCUSSION);
            midi_->playPercussion(60, 127);//high attack velocity
        }
        if (hasAutoDynamics_) {}
        
    }
    else if (timeStep_ == 1) {//2nd quarter
        if (hasMelody_) {// if no melody, no accompaniment/chords, only rhythm can be played
            uchar pitch = melody_[melodyStep_];
            uchar pitchVelocity = melody_[melodyStep_];
            melodyStep_ = (melodyStep_ + 2) % melodyLength_;
            if (pitch != NO_NOTE) {
                if (hasAccompaniment_) {
                  midi_->releaseChannel(CHANNEL_ACCOMPANY);
                  midi_->playAccompaniment(pitch-12, pitchVelocity);
                }
                if (hasChords_) {}
                midi_->releaseChannel(CHANNEL_LEAD);
                midi_->playLead(pitch, pitchVelocity);
            }
        }
        if (hasRhythm_) {//RHYTHM_1_4, RHYTHM_2_4, RHYTHM_3_4, RHYTHM_4_4, RHYTHM_1_2, RHYTHM_2_3
            if (rhythm_ == RHYTHM_2_4 || rhythm_ == RHYTHM_3_4 || rhythm_ == RHYTHM_4_4) {
                midi_->releaseChannel(CHANNEL_PERCUSSION);
                midi_->playPercussion(60, 127);
            }
        }
        if (hasAutoDynamics_) {}
       
        
    }
    else if (timeStep_ == 2) {//3rd quarter
        if (hasMelody_) {// if no melody, no accompaniment/chords, only rhythm can be played
            uchar pitch = melody_[melodyStep_];
            uchar pitchVelocity = melody_[melodyStep_];
            melodyStep_ = (melodyStep_ + 2) % melodyLength_;
            if (pitch != NO_NOTE) {
                if (hasAccompaniment_) {
                  midi_->releaseChannel(CHANNEL_ACCOMPANY);
                  midi_->playAccompaniment(pitch-12, pitchVelocity);
                }
                if (hasChords_) {}
                midi_->releaseChannel(CHANNEL_LEAD);
                midi_->playLead(pitch, pitchVelocity);
            }
        }
        if (hasRhythm_) {//RHYTHM_1_4, RHYTHM_2_4, RHYTHM_3_4, RHYTHM_4_4, RHYTHM_1_2, RHYTHM_2_3
            if (rhythm_ == RHYTHM_3_4 || rhythm_ == RHYTHM_4_4 || rhythm_ == RHYTHM_1_2) {
                midi_->releaseChannel(CHANNEL_PERCUSSION);
                midi_->playPercussion(60, 127);
            }
        }
        if (hasAutoDynamics_) {}
       
               
    }
    else if (timeStep_ == 3) {//4th quarter
        if (hasMelody_) {// if no melody, no accompaniment/chords, only rhythm can be played
            uchar pitch = melody_[melodyStep_];
            uchar pitchVelocity = melody_[melodyStep_];
            melodyStep_ = (melodyStep_ + 2) % melodyLength_;
            if (pitch != NO_NOTE) {
                if (hasAccompaniment_) {
                  midi_->releaseChannel(CHANNEL_ACCOMPANY);
                  midi_->playAccompaniment(pitch-12, pitchVelocity);
                }
                if (hasChords_) {}
                midi_->releaseChannel(CHANNEL_LEAD);
                midi_->playLead(pitch, pitchVelocity);
            }
        }
        if (hasRhythm_) {//RHYTHM_1_4, RHYTHM_2_4, RHYTHM_3_4, RHYTHM_4_4, RHYTHM_1_2, RHYTHM_2_3
            if (rhythm_ == RHYTHM_4_4) {
                midi_->releaseChannel(CHANNEL_PERCUSSION);
                midi_->playPercussion(60, 127);
            }
        }
        if (hasAutoDynamics_) {}
               
    }
    //do this in any case:
    if (hasPedaling_){
        cout << " time: "<< timeStep_ << " pedalingCounter: " << pedalingCounter_ << endl;
        if (pedalingCounter_ == 0) {
            
            midi_->sendControlChange(CHANNEL_LEAD, 64, 0); //turn hold OFF
            midi_->sendControlChange(CHANNEL_ACCOMPANY, 64, 0); //turn hold OFF       
            midi_->sendControlChange(CHANNEL_LEAD, 64, 127); //turn hold ON
            midi_->sendControlChange(CHANNEL_ACCOMPANY, 64, 127); //turn hold OFF
        }
        pedalingCounter_ = (pedalingCounter_ + 1) % pedalingFreq_;   
    }    
    
    timeStep_ = (timeStep_ + 1) % 4;
}
//quarter notes, maybe later we'll need eigth notes
void Conductor::play(uchar pitch, uchar pitchVelocity){
    if (timeStep_ == 0) {//1st quarter 
        if (pitch != NO_NOTE) {
            
            if (hasAccompaniment_) {
                midi_->releaseChannel(CHANNEL_ACCOMPANY);
                midi_->playAccompaniment(pitch-12, pitchVelocity); 
            }
            if (hasChords_) {
                midi_->playChord(pitch-12,10);
                midi_->sendControlChange(CHANNEL_CHORD, 64, 127); //turn hold ON
            }
        }
        if (hasRhythm_) {
            
            midi_->releaseChannel(CHANNEL_PERCUSSION);
            midi_->playPercussion(60, 127);//high attack velocity
        }
        if (hasAutoDynamics_) {}  
       
    }
    else if (timeStep_ == 1) {//2nd quarter
        if (pitch != NO_NOTE) {
            if (hasAccompaniment_) {
                midi_->releaseChannel(CHANNEL_ACCOMPANY);
                midi_->playAccompaniment(pitch-12, pitchVelocity);
            }
            if (hasChords_) {}
        }
        if (hasRhythm_) {
            if (rhythm_ == RHYTHM_2_4 || rhythm_ == RHYTHM_3_4 || rhythm_ == RHYTHM_4_4) {
                midi_->releaseChannel(CHANNEL_PERCUSSION);
                midi_->playPercussion(60, 127);
            }
        }
        if (hasAutoDynamics_) {}
        
    }
    else if (timeStep_ == 2) {//3rd quarter
        if (pitch != NO_NOTE) {
            if (hasAccompaniment_) {
                midi_->releaseChannel(CHANNEL_ACCOMPANY);
                midi_->playAccompaniment(pitch-12, pitchVelocity);
            }
            if (hasChords_) {}
        }
        if (hasRhythm_) {
            if (rhythm_ == RHYTHM_3_4 || rhythm_ == RHYTHM_4_4 || rhythm_ == RHYTHM_1_2) {
                midi_->releaseChannel(CHANNEL_PERCUSSION);
                midi_->playPercussion(60, 127);
            }
        }
        if (hasAutoDynamics_) {}
              
    }
    else if (timeStep_ == 3) {//4th quarter
        if (pitch != NO_NOTE) {
            if (hasAccompaniment_) {
                midi_->releaseChannel(CHANNEL_ACCOMPANY);
                midi_->playAccompaniment(pitch-12, pitchVelocity);
            }
            if (hasChords_) {
                midi_->sendControlChange(CHANNEL_CHORD, 64, 0); //turn hold OFF
                midi_->releaseChannel(CHANNEL_CHORD);
            }
        }
        if (hasRhythm_) {
            if (rhythm_ == RHYTHM_4_4) {
                midi_->releaseChannel(CHANNEL_PERCUSSION);
                midi_->playPercussion(60, 127);
            }
        }
        if (hasAutoDynamics_) {}
        
    }
    //do this in every case:
    if (pitch != NO_NOTE) {//if we dont have NO_NOTE message
        midi_->releaseChannel(CHANNEL_LEAD);
        midi_->playLead(pitch, pitchVelocity);
    }
    if (hasPedaling_){
        cout << " time: "<< timeStep_ << " pedalingCounter: " << pedalingCounter_ << endl;
        if (pedalingCounter_ == 0) {
            
            midi_->sendControlChange(CHANNEL_LEAD, 64, 0); //turn hold OFF
            midi_->sendControlChange(CHANNEL_ACCOMPANY, 64, 0); //turn hold OFF       
            midi_->sendControlChange(CHANNEL_LEAD, 64, 127); //turn hold ON
            midi_->sendControlChange(CHANNEL_ACCOMPANY, 64, 127); //turn hold OFF
        }
        pedalingCounter_ = (pedalingCounter_ + 1) % pedalingFreq_;   
    }    
    if (hasMelody_) {//melody is ignored, but keep counting
            melodyStep_ = (melodyStep_ + 2) % melodyLength_;
    }
    timeStep_ = (timeStep_ + 1) % 4;
}
	
void Conductor::play(uchar pitch, uchar pitchVelocity, uchar accompany, uchar accompanyVelocity) {
    if (timeStep_ == 0) {//1st quarter 
        if (pitch != NO_NOTE) {
            if (hasAccompaniment_) {}
            if (hasChords_) {
                midi_->releaseChannel(CHANNEL_CHORD);
                midi_->sendControlChange(CHANNEL_CHORD, 64, 0); //turn hold OFF
                midi_->playChord(pitch-12,10);
                midi_->sendControlChange(CHANNEL_CHORD, 64, 127); //turn hold ON
            }
        }
        if (hasRhythm_) {
            midi_->releaseChannel(CHANNEL_PERCUSSION);
            midi_->playPercussion(60, 127);//high attack velocity
        }
        if (hasAutoDynamics_) {}  
       
    }
    else if (timeStep_ == 1) {//2nd quarter
        if (pitch != NO_NOTE) {//nothing to do here
            if (hasAccompaniment_) {}
            if (hasChords_) {}
        }
        if (hasRhythm_) {
            if (rhythm_ == RHYTHM_2_4 || rhythm_ == RHYTHM_3_4 || rhythm_ == RHYTHM_4_4) {
                midi_->releaseChannel(CHANNEL_PERCUSSION);
                midi_->playPercussion(60, 127);
            }
        }
        if (hasAutoDynamics_) {}
        
    }
    else if (timeStep_ == 2) {//3rd quarter
        if (pitch != NO_NOTE) {//nothing to do here
            if (hasAccompaniment_) {}
            if (hasChords_) {}
        }
        if (hasRhythm_) {
            if (rhythm_ == RHYTHM_3_4 || rhythm_ == RHYTHM_4_4 || rhythm_ == RHYTHM_1_2) {
                midi_->releaseChannel(CHANNEL_PERCUSSION);
                midi_->playPercussion(60, 127);
            }
        }
        if (hasAutoDynamics_) {}
              
    }
    else if (timeStep_ == 3) {//4th quarter
        if (pitch != NO_NOTE) {//nothing to do here
            if (hasAccompaniment_) {}
            if (hasChords_) {}
        }
        if (hasRhythm_) {
            if (rhythm_ == RHYTHM_4_4) {
                midi_->releaseChannel(CHANNEL_PERCUSSION);
                midi_->playPercussion(60, 127);
            }
        }
        if (hasAutoDynamics_) {}
        
    }
    //do this in every case:
    if (pitch != NO_NOTE) {//if we dont have NO_NOTE message
        midi_->releaseChannel(CHANNEL_LEAD);
        midi_->playLead(pitch, pitchVelocity);
    }
    if (accompany != NO_NOTE) {
        midi_->releaseChannel(CHANNEL_ACCOMPANY);
        midi_->playAccompaniment(accompany, accompanyVelocity); 
    }
    if (hasPedaling_){
        cout << " time: "<< timeStep_ << " pedalingCounter: " << pedalingCounter_ << endl;
        if (pedalingCounter_ == 0) {
            
            midi_->sendControlChange(CHANNEL_LEAD, 64, 0); //turn hold OFF
            midi_->sendControlChange(CHANNEL_ACCOMPANY, 64, 0); //turn hold OFF       
            midi_->sendControlChange(CHANNEL_LEAD, 64, 127); //turn hold ON
            midi_->sendControlChange(CHANNEL_ACCOMPANY, 64, 127); //turn hold OFF
        }
        pedalingCounter_ = (pedalingCounter_ + 1) % pedalingFreq_;   
    }    
    if (hasMelody_) {//melody is ignored, but keep counting
            melodyStep_ = (melodyStep_ + 2) % melodyLength_;
    }
    timeStep_ = (timeStep_ + 1) % 4;
}

void Conductor::playImmediate(uchar pitch, uchar velocity) {
    midi_->releaseChannel(CHANNEL_LEAD);
    midi_->playLead(pitch, velocity);
}	

Instrument Conductor::getInstrument() {
    return instrument_;
}
 
int Conductor::getAccompaniment() {
    return accompaniment_;
}
 
Chords Conductor::getChords() {
    return chords_;
}

Rhythm Conductor::getRhythm() {
    return rhythm_;
}
     
Dynamics Conductor::getDynamics() {
    return dynamics_;
}

bool Conductor::getAutomaticDynamics() {
    return hasAutoDynamics_;
}
   
bool Conductor::getHarmony() {
    return hasHarmony_;
}
    
vector<uchar> Conductor::getMelody() {
    return melody_;
}
    
bool Conductor::getPedaling() {
    return hasPedaling_;
}
     
bool Conductor::getReverberation() {
    return hasReverb_;
}
    
//make accompaniment the same as the lead
void Conductor::setInstrument(Instrument instrument) {
    if (instrument == INSTRUMENT_CLASSIC) {
        midi_->sendProgramChange(CHANNEL_LEAD, 0);
        midi_->sendProgramChange(CHANNEL_ACCOMPANY, 0);
        midi_->sendProgramChange(CHANNEL_CHORD, 48);
        midi_->sendProgramChange(CHANNEL_PERCUSSION, 118);
    }
    else if (instrument == INSTRUMENT_CRAZY) {
        midi_->sendProgramChange(CHANNEL_LEAD, 115);
        midi_->sendProgramChange(CHANNEL_ACCOMPANY, 115);
        midi_->sendProgramChange(CHANNEL_CHORD, 122);
        midi_->sendProgramChange(CHANNEL_PERCUSSION, 121);
    }
    else if (instrument == INSTRUMENT_WIND) {
        midi_->sendProgramChange(CHANNEL_LEAD, 56);
        midi_->sendProgramChange(CHANNEL_ACCOMPANY, 56);
        midi_->sendProgramChange(CHANNEL_CHORD, 66);
        midi_->sendProgramChange(CHANNEL_PERCUSSION, 118);
    }
    instrument_ = instrument;
}
	
//make paramOne == 0 mean that the accompaniment plays the same note, just lower volume, for the time being
void Conductor::setAccompaniment(bool isOn, int paramOne) {
    hasAccompaniment_ = isOn;
    accompaniment_ = paramOne;
}

//TODO: different chord options	
void Conductor::setChords(bool isOn, Chords chords) {
    hasChords_ = isOn;
    chords_ = chords;
}
	
void Conductor::setRhythm(bool isOn, Rhythm rhythm) {
    hasRhythm_ = isOn;
    rhythm_ = rhythm;
}
	
//TODO: do we want to have this??
void Conductor::modifyRhythm(int paramOne, int paramTwo) {}
	
void Conductor::setDynamics(Dynamics dynamics) {
    // DYNAMICS_PIANO, DYNAMICS_FORTE, DYNAMICS_PIANISSIMO, DYNAMICS_FORTISSIMO 
    dynamics_ = dynamics;
    if (dynamics ==  DYNAMICS_PIANO) {//lead volume: 60
        midi_->sendControlChange(CHANNEL_LEAD, 7, 45);
        midi_->sendControlChange(CHANNEL_ACCOMPANY, 7, 30);
        midi_->sendControlChange(CHANNEL_CHORD, 7, 35);
        midi_->sendControlChange(CHANNEL_PERCUSSION, 7, 15);
        
    }
    else if (dynamics ==  DYNAMICS_FORTE) {//lead volume: 90
        midi_->sendControlChange(CHANNEL_LEAD, 7, 70);
        midi_->sendControlChange(CHANNEL_ACCOMPANY, 7, 45);
        midi_->sendControlChange(CHANNEL_CHORD, 7, 60);
        midi_->sendControlChange(CHANNEL_PERCUSSION, 7, 30);
        
    }
    else if (dynamics ==  DYNAMICS_PIANISSIMO) {//lead volume: 30
        midi_->sendControlChange(CHANNEL_LEAD, 7, 25);
        midi_->sendControlChange(CHANNEL_ACCOMPANY, 7, 15);
        midi_->sendControlChange(CHANNEL_CHORD, 7, 20);
        midi_->sendControlChange(CHANNEL_PERCUSSION, 7, 10);
        
    }
    else if (dynamics ==  DYNAMICS_FORTISSIMO) {//lead volume: 127
        midi_->sendControlChange(CHANNEL_LEAD, 7, 127);
        midi_->sendControlChange(CHANNEL_ACCOMPANY, 7, 90);
        midi_->sendControlChange(CHANNEL_CHORD, 7, 110);
        midi_->sendControlChange(CHANNEL_PERCUSSION, 7, 55);
        
    }
}

//TODO: determine algorithm	
void Conductor::setAutomaticDynamics(bool isOn) {
    hasAutoDynamics_ = isOn;
}

//TODO: set up a data structure	
void Conductor::setHarmony(bool isOn, int paramOne) {
    hasHarmony_ = isOn;
    harmony_ = paramOne;
}
	

void Conductor::setMelody(vector<uchar> melody) {//passed by copy to prevent simultaneous access chaos  
	melodyStep_ = 0;
	melody_ = melody;
    melodyLength_ = melody_.size();
    if ( (melodyLength_ % 2 ) != 0)//check if right format, if not disregard last information
        melodyLength_--;
    if (melodyLength_ == 0)//if no notes in vector, nothing to play 
        hasMelody_ = false;
    else 
        hasMelody_ = true;
}

void Conductor::setPedaling(bool isOn, int frequency) {
    hasPedaling_ = isOn;
    pedalingFreq_ = frequency;
    pedalingCounter_ = 0;
}

void Conductor::setReverberation(bool isOn) {
    hasReverb_ = isOn;
    if (isOn) {
        midi_->sendControlChange(CHANNEL_LEAD, 91,127);//turn on
        midi_->sendControlChange(CHANNEL_ACCOMPANY, 91,127);//turn on
    }
    else {
        midi_->sendControlChange(CHANNEL_LEAD, 91,0); //turn off
        midi_->sendControlChange(CHANNEL_ACCOMPANY, 91,0);//turn on
    }
}

void Conductor::pressPanicButton() {
    midi_->releaseChannel(CHANNEL_CHORD);//in case a message is lost
    midi_->sendControlChange(CHANNEL_CHORD, 64, 0); //turn hold OFF
   	midi_->panic();
}

void Conductor::setModulation(uchar position) {
    if (position == 0) {
        midi_->sendControlChange(CHANNEL_LEAD, 1, 0);
        midi_->sendControlChange(CHANNEL_ACCOMPANY, 1, 0);
        midi_->sendControlChange(CHANNEL_CHORD, 1, 0);
        midi_->sendControlChange(CHANNEL_PERCUSSION, 1, 0);
    }
    else {
        midi_->sendControlChange(CHANNEL_LEAD, 1, position);
        midi_->sendControlChange(CHANNEL_ACCOMPANY, 1, position);
        midi_->sendControlChange(CHANNEL_CHORD, 1, position);
        midi_->sendControlChange(CHANNEL_PERCUSSION, 1, position);
    }
}

void Conductor::setPan(uchar position) {
    cout << "pan" << endl;
    midi_->sendControlChange(CHANNEL_LEAD, 1, position);
    //midi_->sendControlChange(CHANNEL_LEAD, 5, position);
}
}
