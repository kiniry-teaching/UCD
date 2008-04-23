#include "Interpreter.h"
#include "../type.h"
#include "../rai/ShapeId.h"
#include "../audio/Conductor.h"
#include "../rai/Analyser/ShapeMatches.h"
#include "../rai/Analyser/ShapeMatch.h"

using namespace std;
using namespace audio;
using namespace interpreter;

Interpreter::Interpreter()
{
	
	
}

Interpreter::~Interpreter()
{
	
	
}

Shape* Interpreter::getShape()
{
	return shape;
	
}

bool Interpreter::mapShape()
{
	/**
	 * @Pseudo_code
	 * if(user_shape == shape)
	 *	if(shapeMap){
			return true;
	 *	}else{
			return false;
		}
	
	 	return true;
	 	
	 */	
	 
	
	return true;
}

int Interpreter::shapeMatching(ShapeMatches* shapeMatches)
{
	
	
	// Dealing with ShapeMatches------------------------------------------
	//ShapeMatches * shapeMatches;
 
	for(uint i = 0; i < shapeMatches->length(); i++)
	{
  		// Get top-level gesture matches
  		ShapeMatch * shapeMatch = (*shapeMatches)[i];
  		
  		// Get speed/acceleration sub-level gesture matches (if any)
  		for(uint j = 0; j < shapeMatch->shapeMatches()->length(); j++)
  		{
    		ShapeMatch * shapeMatchSub = (*shapeMatch->shapeMatches())[i];
    		//mapSubShapeIdToAudio
    		shapemovement(shapeMatchSub->shape());
  		}
  		//maping shape id to the audio
  		shapemovement(shapeMatch->shape());
  		
	}
	return 0;
}

void Interpreter::shapemovement(Shape const * const shapemovement) const{
	
	//determine the values for the music from the movement.
	//ouput pass to the audio class
	//Shape matching with dynamics audio
	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(DYNAMICS_PIANO)
	 * @result setDynamics to DYNAMICS_PIANO
	 */
	 	
		if(shapemovement->shapeId() == esid::DYNAMICS_PIANO)
			con->setDynamics(DYNAMICS_PIANO);
		
	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(DYNAMICS_FORTE)
	 * @result setDynamics to DYNAMICS_FORTE
	 */
	 	
		if(shapemovement->shapeId() == esid::DYNAMICS_FORTE)
			con->setDynamics(DYNAMICS_FORTE);	
	
	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(DYNAMICS_PIANISSIMO)
	 * @result setDynamics to DYNAMICS_PIANISSIMO
	 */
	 	
		if(shapemovement->shapeId() == esid::DYNAMICS_PIANISSIMO)
			con->setDynamics(DYNAMICS_PIANISSIMO);	
	
	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(DYNAMICS_FORTISSIMO )
	 * @result setDynamics to DYNAMICS_FORTISSIMO 
	 */
	 	
		if(shapemovement->shapeId() == esid::DYNAMICS_FORTISSIMO)
			con->setDynamics(DYNAMICS_FORTISSIMO);	
	
//Shape matching with rhythm audio		
	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(RHYTHM_1_4 )
	 * @result setRhythm to RHYTHM_1_4 
	 */
	 	
		if(shapemovement->shapeId() == esid::RHYTHM_1_4)
			con->setRhythm(true,RHYTHM_1_4);			
	 				
	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(RHYTHM_2_4 )
	 * @result setRhythm to RHYTHM_2_4 
	 */
	
		if(shapemovement->shapeId() == esid::RHYTHM_2_4)
			con->setRhythm(true,RHYTHM_2_4);

	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(RHYTHM_3_4 )
	 * @result setRhythm to RHYTHM_3_4 
	 */
	
		if(shapemovement->shapeId() == esid::RHYTHM_3_4)
			con->setRhythm(true,RHYTHM_3_4);

	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(RHYTHM_4_4 )
	 * @result setRhythm to RHYTHM_4_4 
	 */
	
		if(shapemovement->shapeId() == esid::RHYTHM_4_4)
			con->setRhythm(true,RHYTHM_4_4);

	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(RHYTHM_1_2 )
	 * @result setRhythm to RHYTHM_1_2 
	 */
	
		if(shapemovement->shapeId() == esid::RHYTHM_1_2)
			con->setRhythm(true,RHYTHM_1_2);

	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(RHYTHM_2_3)
	 * @result setRhythm to RHYTHM_2_3 
	 */
	
		if(shapemovement->shapeId() == esid::RHYTHM_2_3)
			con->setRhythm(true,RHYTHM_2_3);	

	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(RHYTHM_NONE  )
	 * @result setRhythm to RHYTHM_NONE  
	 */
	
		if(shapemovement->shapeId() == esid::RHYTHM_NONE )
			con->setRhythm(false,RHYTHM_NONE);

  //Shape matching with Chords audio	

	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(CHORDS_FIRST  )
	 * @result  setChords to CHORDS_FIRST  
	 */
	
		if(shapemovement->shapeId() == esid::CHORDS_FIRST )
			con-> setChords(true,CHORDS_FIRST);

	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(CHORDS_SECOND  )
	 * @result  setChords to CHORDS_SECOND  
	 */
	
		if(shapemovement->shapeId() == esid::CHORDS_SECOND )
			con-> setChords(true,CHORDS_SECOND);


	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(CHORDS_THIRD  )
	 * @result  setChords to CHORDS_THIRD  
	 */
	
		if(shapemovement->shapeId() == esid::CHORDS_THIRD )
			con->setChords(true,CHORDS_THIRD);


	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(CHORDS_ONEOFF )
	 * @result  setChords to CHORDS_ONEOFF
	 */
	
		if(shapemovement->shapeId() == esid::CHORDS_123 )
			con-> setChords(true,CHORDS_123);


	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(CHORDS_NONE  )
	 * @result  setChords to RHYTHM_NONE  
	 */
	
		if(shapemovement->shapeId() == esid::CHORDS_NONE  )
			con-> setChords(true,CHORDS_NONE );


  //Shape matching with Instrument audio	

	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(INSTRUMENT_CLASSIC)
	 * @result setInstrument to INSTRUMENT_CLASSIC  
	 */
	
		if(shapemovement->shapeId() == esid::INSTRUMENT_CLASSIC )
			con->setInstrument(INSTRUMENT_CLASSIC);

	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(INSTRUMENT_CRAZY)
	 * @result setInstrument to INSTRUMENT_CRAZY  
	 */
	
		if(shapemovement->shapeId() == esid::INSTRUMENT_CRAZY )
			con->setInstrument(INSTRUMENT_CRAZY);

	/**
	 * if the shape of the gesture been create(shapemovement)
	 * is equal to the audio command(INSTRUMENT_WIND)
	 * @result setInstrument to INSTRUMENT_WIND  
	 */
	
		if(shapemovement->shapeId() == esid::INSTRUMENT_WIND )
			con->setInstrument(INSTRUMENT_WIND);
				
	

}		 
	
	



