#ifndef INTERPRETER_H_
#define INTERPRETER_H_

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
		void getShape(); 
		
		//Determinine the Mapping of the shape to audio commands
		bool mapShape();
		
		
private:   

		/*Calling the frame(point) from track
		 * Distance from each frame(point) to another
		 */
        int calSpeed();
        
        //The time it takes from one frame(point) to another
        int calTime();
        
        //the initial map shape 
        String map;
};

#endif /*INTERPRETER_H_*/
