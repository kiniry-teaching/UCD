#ifndef INTERPRETER_H_
#define INTERPRETER_H_
#include "../rai/Analyser/ShapeMatches.h"
#include "../rai/Analyser/Shape.h"
#include "../audio/Conductor.h"


using namespace std;

using namespace audio;
using namespace interpreter;

/**
 * 
 * @author SA
 */
class Interpreter
{
public:

	
		//The constructor for the interpreter
		Interpreter();
		
		//The deconstructor for the interpreter
		virtual ~Interpreter();
		
		/*Uses the identity of shape to convert to the commands
		 * Specific control change that is allow from the audio??
		 */
		Shape* getShape(); 
		
		//Determinine the Mapping of the shape to audio commands
		bool mapShape();

                 
         //Mapping from the shape given into audio control(chords, dynamic, rythmic, texture)
         // return integer of the last frame(point) use.
         
         int shapeMatching(ShapeMatches*);
         void shapemovement(Shape const * const) const;
         
  
  
private:
		Shape* shape;
		Conductor* con; 
		

////		ShapeMovement shapeMovement;

            
	
};

#endif /*INTERPRETER_H_*/
