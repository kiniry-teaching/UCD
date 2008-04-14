#ifndef MIDIRECORDER_H_
#define MIDIRECORDER_H_

#include <string>
#include <vector>
#include <fstream>
#include <iostream>
#include "../type.h"
using namespace std;

namespace audio
{
    
/**
 * Records a MIDI file.
 * @author ED 
 * @version 1.0
 */
class MidiRecorder
{
public:
	/**
	 * Constructs a new MidiRecorder. 
	 */
	MidiRecorder();
	
    /**
     * Destroy this MidiRecorder.
     */
	virtual ~MidiRecorder();
	
	/** 
	 * Opens a new file to write to and sets up the MIDI header. 
	 * @param noTracks number of tracks to be used
	 * @returns Returns false if, for any reason, fails to open a file.
	 */
	bool openFile();
		
	/** 
	 * Opens the given file to write to.
	 * This will overwrite all old contents of the file. 
	 * @param fileName fileName of the new file 
	 * @param noTracks number of tracks to be used
	 * @returns false if, for any reason, fails to open a file.
	 */
	bool openFile(string fileName);
		
	/** 
	 * Closes (saves) the file.
	 * The previously filled buffers will be written to file in
	 * the correct order.
	 * @returns true if file successfully closed
	 */
	bool closeFile();
		
	/** 
	 * Writes a new event to buffer.
	 * @param event message to be written to file
	 * @param trackNo trackNo number this event belongs to
	 * @returns true if write is successful
	 */
	bool write(vector<uchar> event, ulong deltaTime);
		
private:
	string fileName_;
    ofstream myFile_;
	//buffer
	vector<uchar> buffer_;

};

}
#endif /*MIDIRECORDER_H_*/
