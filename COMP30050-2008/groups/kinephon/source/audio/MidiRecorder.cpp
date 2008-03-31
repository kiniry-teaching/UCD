#include "MidiRecorder.h"

namespace audio
{
    
MidiRecorder::MidiRecorder() {
    
   
}

MidiRecorder::~MidiRecorder() {}

bool MidiRecorder::openFile(int noTracks) {
    myFile_.open("writeFile.mid", ios::out | ios::binary);
    /*header chunk looks like: 
      4D 54 68 64 (MThd) 00 00 00 06 (FIXED) ff ff nn nn dd dd
      # ff ff is the file format. There are 3 formats:
        (0 - single-track; 1 - multiple tracks, synchronous; 2 - multiple tracks, asynchronous
      # nn nn is the number of tracks in the midi file.
      # dd dd is the number of delta-time ticks per quarter note. 
    */
    char header_first[8] = { 'M', 'T', 'h', 'd', 0, 0, 0, 6 };
    myFile_.write(header_first, 8);
    
    //this will vary
    //TODO: determine the best delta tick time
    char header_second[6] = { 0, 0, 0, 1, 0, 72 }; 
    myFile_.write(header_second, 6);
    
    //don't write the track header, since we could only write half of it anyway...

    return false;
}

bool MidiRecorder::openFile(string fileName, int noTracks) {
    
    return false;
}

bool MidiRecorder::closeFile() {
    //have to write buffer into file with all the missing header information
    /*track chunks, header:
      4D 54 72 6B (MTrk) xx xx xx xx (lenght of track not including header in bytes)
     
     */
    char track_first[4] = { 'M', 'T', 'r', 'k' };
    myFile_.write(track_first, 4);
    //determine size of buffer in bytes and covert them into char size chunks
    char track_size[4] = { 0, 0, 0, 0};
    //TODO: this needs work 
    track_size[3] = trackOne_.size() % 128;
    track_size[2] = (trackOne_.size() % 16384) - track_size[3];
    track_size[1] = (trackOne_.size() % 2097152) - track_size[2] - track_size[3];
    track_size[0] = trackOne_.size() >> 12;
    myFile_.write(track_size, 4);
    
    //need a vector, not an array, so take the address of the first element, ugly but don't want to copy the whole thing
    //and we need the array of chars not unsigned ones
    myFile_.write((char*)&trackOne_[0], trackOne_.size());
     
    myFile_.close();
    return false;
}

bool MidiRecorder::write(vector<uchar> event, int trackNo) {
    //add delta time, need to know if it's a NOTE ON/OFF, these have to be equally spaced use the 72 as set for length of quarter note,
    //the rest can have delta time 0
    if (event[0] < 160 && event[0] >= 144)//NOTE ON
        trackOne_.push_back(72);
    else if (event[0] < 143 && event[0] >= 128)//NOTE OFF
        trackOne_.push_back(72);
    else
        trackOne_.push_back(0);
        
        
    //add midi event data:
    for (int i = 0; i < event.size(); i++)
        trackOne_.push_back(event[i]); 
    return false;
}



    
    
}
