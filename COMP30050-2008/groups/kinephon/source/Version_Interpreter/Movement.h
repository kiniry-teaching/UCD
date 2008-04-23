#ifndef MOVEMENT_H_
#define MOVEMENT_H_
#include "../rai/Recorder/Track.h"
#include "../audio/Conductor.h"
#include "../audio/Channel.h"
#include <map>
#include "../type.h"


/**
 * The movement of the gesture/track
 * Depending on the different control of the music we have
 * The motion that response to the shape in general
 * It works with the track class 
 * @author SA
 */
 

 using namespace std;
using namespace audio;
 using namespace interpreter;
 
class movement
{
public:
	    //The Constructor for the movement
		movement(Conductor* music);
		
		//The deconstructor for the movement		
		virtual ~movement();

        //the main work of the interpreter converting the movement into commands
        // return integer of the last frame(point) use.
        int tracking(Track*);
        //determining how the movement of the audio works???
        void audioMovement(Track const* const) ;
        
        
private:

		Conductor* music;
		map<irid,Instrument> mapping1;
		int mel;
		
};

#endif /*MOVEMENT_H_*/
