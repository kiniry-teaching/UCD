#include "movement.h"
#include "Conductor.h"
#include "Track.h"
#include "Frame.h"
#include "ShapeId.h"
#include <vector>
#include <map>
#include <cstdlib>
#include "Melody.h"
#include <vector>

using namespace std;
using namespace audio;
using namespace interpreter;

movement::movement(	Conductor* music)
{
	this->music = music;
	
}

movement::~movement()
{
	
	
}


int movement::tracking(Track* track)
{
	
	// Dealing with Tracks------------------------------------------------
//Track * track;
 
// Get the IR blob id that this track relates
//setActiveIRId(track->iid());
 
// Iterate through each frame
	Frame * frame = track->first();
	while(frame != 0)
	{
  		//doSomethingBasedOnFrame(frame);
  		//adding the movement together
  		if(this != 0)
  			 track->iid();
  			
  		frame = frame->next();
	}
	
	 return 0;
}  
	/**
	 * @Pseudo_code
	 *	for(int i = 0; i < track.leght(); i++)
	 *	movement-->commands(soft, loud, quiet, p, mp, mf, f)
	 * 
	 */
	
void movement::audioMovement(Track  const* const track)
{
   /** spliting the screen into notes(column) and octives(rows)
	* create 12notes, one octives(12notes)
	* result1 = Horizontal(column) division of the screen divides by the 12notes result to the actual notes to be played
	* result2 = veritcal(rows) division of the screen divides by the  10 octaves result to the octaves to be played
	* result1 + (result2*12)
	* use uchar for the notes and the octives
	*/
	
	
 	const uint NUM_NOTES = 12;
  	const uint NUM_OCTAVES = 10;

  	// Screen width and height will have to come from the window code, but we don't have this yet.
  	const uint SCREEN_WIDTH = 800;
  	const uint SCREEN_HEIGHT = 600;

  	// For this example, I'm just going to take the last move recorded, but other things could be done
		
	Frame * frame = track->first()->last();
	          
	 //the instument sound       
   if(!(mapping1[track->iid()])){
    	 /*pick some instrument/effect*/
    	switch(rand()% 3){
    	case 0: mapping1[track->iid()] = INSTRUMENT_CLASSIC;
    	break;
    	case 1: mapping1[track->iid()] = INSTRUMENT_CRAZY;
    	break;
    	case 2: mapping1[track->iid()] = INSTRUMENT_WIND;
    	break;
    	}
    	
    }
    music->setInstrument(mapping1[track->iid()]);

    static int test = 0;
    static int musicVar = 0;
    switch(test){
    case 0: music->setDynamics( DYNAMICS_PIANISSIMO);
    break;
    case 1: music->setDynamics( DYNAMICS_PIANO);//soft
        break;
    case 2: music->setDynamics(  DYNAMICS_FORTISSIMO);
        break;
    case 3: music->setDynamics( DYNAMICS_FORTE);//loud
        break;
        
    default: test = -1;
    }
    //cout << test << endl;
    test++;
    //variable for the melody been played
    //if there is any code to check when the melody ends
    //vector<uchar> notes;
     //music->setMelody(notes);//no melody
    if(musicVar == 0){
    	mel = rand()% Melody::meloding.size();
        music->setMelody(Melody::meloding[mel]);
        music->setAccompaniment(true);
        music->setChords(true,CHORDS_FIRST);
        music->setRhythm(true,  RHYTHM_2_3);
    }
    musicVar++;
    if(musicVar == 20){
    	musicVar = 0; 
    }
 

  	// Calculate the note as the horizontal position of the movement

  		uchar note = frame->x() * NUM_NOTES / SCREEN_WIDTH;

 	 // Calculate the octave as the vertical position of the movement

  		uchar octave = frame->y() * NUM_OCTAVES / SCREEN_HEIGHT;
	
  		music->play(note, octave, 50);
  		
  		//music->play();
  		
}