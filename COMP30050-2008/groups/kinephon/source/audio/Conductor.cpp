#include "Conductor.h"

Conductor::Conductor():
	midi_(NULL),
	timeStep_(0),
	melodyStep_(0),
	hasAccompaniment_(false),
	hasChords_(false),
	hasRhythm_(false),
	hasAutoDynamics_(false),
	hasHarmony_(false),
	hasReverb_(false),
	rhythm_(RHYTHM_NONE),
	chords_(CHORDS_NONE),
	dynamics_(DYNAMICS_FORTE),
	texture_(TEXTURE_POLY)
{}

Conductor::~Conductor()
{
	delete midi_;
}

bool Conductor::initialize(){
	midi_ = new MidiPlayer();
	if(!midi_->initialize())
    	return false;
    else
    	return true; 
}

//expects 1/4 note steps
void Conductor::play(){
	if(timeStep_ == 0){ 
        midi_->panic();
        midi_->panicChords();
		midi_->playLead(melody_[melodyStep_], melody_[melodyStep_ + 1]);
        midi_->playChord(melody_[melodyStep_], 127);
		timeStep_++;
		
	}
	else if(timeStep_ == 1){
		midi_->panic();
		midi_->playLead(melody_[melodyStep_], melody_[melodyStep_ + 1]);
        timeStep_++;
		
	}
	else if(timeStep_ == 2){
		midi_->panic();
		midi_->playLead(melody_[melodyStep_], melody_[melodyStep_ + 1]);
		timeStep_++;
		
	}
	else if(timeStep_ == 3){
		midi_->panic();
		midi_->playLead(melody_[melodyStep_], melody_[melodyStep_ + 1]);
		timeStep_ = 0;
		
	}
    melodyStep_ = (melodyStep_ + 2) % melody_.size();
}
	
void Conductor::play(uchar pitch){}
	
void Conductor::play(uchar pitch, uchar accompany){}

void Conductor::playImmediate(uchar pitch, uchar velocity){}
	
void Conductor::setLeadInstrument(uchar instrument){}
	
void Conductor::setAccompaniment(bool isOn, int paramOne){}
	
void Conductor::setChords(bool isOn, Chords chords){}
	
void Conductor::setRhythm(bool isOn, Rhythm rhythm){}
	
void Conductor::modifyRhythm(int paramOne, int paramTwo){}
	
void Conductor::setDynamics(Dynamics dynamics){}
	
void Conductor::setAutomaticDynamics(bool isOn){}
	
void Conductor::setHarmony(bool isOn, int paramOne){}
	
//passed by copy	
void Conductor::setMelody(vector<uchar> melody){
	melodyStep_ = 0;
	melody_ = melody;
    midi_->sendProgramChange(CHANNEL_CHORD, 49);
}

void Conductor::setPedaling(bool isOn, int frequency){}
	
void Conductor::setTexture(Texture texture){}
	
void Conductor::setReverberation(bool isOn){}

void Conductor::pressPanicButton(){
	midi_->panic();
    midi_->panicChords();
}
