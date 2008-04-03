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
    
    char header_second[6] = { 0, 0, 0, 1,0, 0x60 }; 
    myFile_.write(header_second, 6);
    
    return true;
}

bool MidiRecorder::openFile(string fileName, int noTracks) {
    
    return false;
}

bool MidiRecorder::closeFile() {
    /*track chunks, header:
      4D 54 72 6B (MTrk) xx xx xx xx (lenght of track not including header in bytes) 
     */
    char track_first[4] = { 'M', 'T', 'r', 'k' };
    char end_of_track[4] = {0x00, 0xFF, 0x2F, 0x00};//absolutely necessary
    char time_signature[7] = {0xFF, 0x58, 0x04, 0x04, 0x02, 0x24, 0x08};//opt 
    char tempo[7] = {0x00, 0xFF, 0x51, 0x03, 0x07, 0xA1, 0x20};//opt
    char track_name[7] = { 0xFF, 0x03, 0x04 , 't', 'e', 's', 't'};//opt
 
    
    //TODO: determine size if track in right format
    char track_size[4] = { 0, 0, 0, 76};
     
    myFile_.write(track_first, 4);
    myFile_.write(track_size, 4);
    
   // myFile_.write(track_name, 7);
    myFile_.write(time_signature, 7);
    myFile_.write(tempo, 7);
    
    
    myFile_.write((char*)&trackOne_[0], 55);//actual data
    myFile_.write(end_of_track, 4);
    myFile_.close();
    
    //cout << "real track size: " << trackOne_.size() << endl;
    //cout << "track size: " << track_size[0] << " " << track_size[1] << " " << track_size[2] << " "<< track_size[3] << endl; 
    return true;
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
    for (uchar i = 0; i < event.size(); i++)
        trackOne_.push_back(event[i]); 
    
    cout << "writing: " << (int) event[0] << "  " << (int) event[1] << endl;
    return true;
}



    
    
}
