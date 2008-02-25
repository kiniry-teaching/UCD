#ifndef AUDIORECORDER_H_
#define AUDIORECORDER_H_

#include <string>
#include <vector>
using namespace std;
/*
 * Author:	ED
 *
 * Writes a Midi file.
 * 
 */

class AudioRecorder
{
public:
	/* Initializes a new AudioRecorder */
	AudioRecorder();
	
	/* Anything to clean up? */
	virtual ~AudioRecorder();
	
public://Properties
		

public://Methods
		/* 
		 * Opens new file to write to and sets up the header 
		 * @returns Returns false if, for any reason, fails to open a file.
		 */
		bool OpenFile();
		
		/* 
		 * Opens the given file to write to.
		 * This will overwrite all old contents of the file. 
		 * @returns Returns false if, for any reason, fails to open a file.
		 */
		bool OpenFile(string fileName);
		
		/* 
		 * Closes (saves) the file.
		 */
		bool CloseFile();
		
		/* 
		 * Writes a new event to file. 
		 * Note: the format of the argument might change, reaserch needed.
		 */
		bool Write(vector<unsigned char> *event);
		
private:
	string _filename;
	//other needed I/O devices, needs further research.
};

#endif /*AUDIORECORDER_H_*/
