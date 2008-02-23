#ifndef RECORDERSOUND_H_
#define RECORDERSOUND_H_

/*
 * Autor: Sumbo
 * This will record the different sound produced and store the sound in some file
 * It will also allow the same music that is previous play to be repeated
 */

class RecorderSound
{
public:
		//The constructor for the recordersound
		RecorderSound();
		
		//The deconstructor for the recordersound
		virtual ~RecorderSound();
		
		//for recording the sound
		void record();
		
		//for repeating the sound
		void repeat();
		
};

#endif /*RECORDERSOUND_H_*/
