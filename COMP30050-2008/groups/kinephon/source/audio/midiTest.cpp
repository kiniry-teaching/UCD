#include "Conductor.h"
#include "MidiRecorder.h"
#include <string>
#include <fstream>
#include <iostream>
using namespace std;
using namespace audio;

// Platform-dependent sleep routines.
#if defined(__WINDOWS_MM__)
  #include <windows.h>
  #define SLEEP( milliseconds ) Sleep( (DWORD) milliseconds ) 
#else // Unix variants
  #include <unistd.h>
  #define SLEEP( milliseconds ) usleep( (unsigned long) (milliseconds * 1000.0) )
#endif

/**
 * @author:	ED
 *
 * Demo test program for MidiPlayer.
 */
#ifdef __ED__
int main(){
   
    string portName = "Synth input port";
	Conductor audio;
	if(!audio.initialize(true, portName))
    	exit( EXIT_FAILURE ); 

    vector<uchar> melody(60);
    melody[0] = 60; melody[1] = 127;
    melody[2] = NO_NOTE; melody[3] = 60;
    melody[4] = 64; melody[5] = 60;
    melody[6] = 67; melody[7] = 60;
    melody[8] = 69; melody[9] = 60;
    melody[10] = 70; melody[11] = 127;
    melody[12] = NO_NOTE; melody[13] = 60;
    melody[14] = 69; melody[15] = 60;
    melody[16] = 67; melody[17] = 127;
    melody[18] = 64; melody[19] = 60;
    
    
     melody[20] = 65; melody[21] = 127;
    melody[22] = NO_NOTE; melody[23] = 60;
    melody[24] = 69; melody[25] = 60;
    melody[26] = 72; melody[27] = 60;
    melody[28] = 74; melody[29] = 60;
    melody[30] = 75; melody[31] = 127;
    melody[32] = NO_NOTE; melody[33] = 60;
    melody[34] = 74; melody[35] = 60;
    melody[36] = 72; melody[37] = 127;
    melody[38] = 69; melody[39] = 60;
    
     melody[40] = 67; melody[41] = 127;
    melody[42] = NO_NOTE; melody[43] = 60;
    melody[44] = 71; melody[45] = 60;
    melody[46] = 74; melody[47] = 60;
    melody[48] = 76; melody[49] = 60;
    melody[50] = 77; melody[51] = 127;
    melody[52] = NO_NOTE; melody[53] = 60;
    melody[54] = 76; melody[55] = 60;
    melody[56] = 74; melody[57] = 127;
    melody[58] = 71; melody[59] = 60;
   
   
//for testing automation
// for each true, the melody is being played
bool piano = false;
bool pianissimo = false;
bool forte = true;
bool fortissimo = false;   

bool testingPlayOnly = true;
bool testingPlayLead = true;
bool testingPlayLeadAcc = true;

int tempo = 200; //set the miliseconds to sleep between each note, here for once
//uncomment these for overall settings, or include them somewhere in the middle of the code
//audio.setPedaling(true, 16);
//audio.setInstrument(INSTRUMENT_CRAZY);
//audio.setModulation(127);
//audio.setPan(127);
audio.setReverberation(true);
if (testingPlayOnly) {
    
   cout << "playing only preset settings"<< endl; 
    audio.setMelody(melody);
    audio.setAccompaniment(true);
    audio.setChords(true,CHORDS_FIRST);
    audio.setRhythm(true, RHYTHM_2_3);	
    int i = 0;
    if (piano) {
        audio.setDynamics(DYNAMICS_PIANO);
        i = 0;
        while(i < 60){
            audio.play();    
            SLEEP(tempo);
            i += 2;
        }
    }    
    if (pianissimo) {
        audio.setDynamics(DYNAMICS_PIANISSIMO);
        i = 0;
        while(i < 60){
            audio.play();    
            SLEEP(tempo);
            i += 2;
        }
    }
    if (forte) { 
        audio.setDynamics(DYNAMICS_FORTE);
        i = 0;
        while(i < 60){
            audio.play();    
            SLEEP(tempo);
            i += 2;
        }
    }
    if (fortissimo) {
        audio.setDynamics(DYNAMICS_FORTISSIMO);
        i = 0;
        while(i < 60){
            audio.play();    
            SLEEP(tempo);
            i += 2;
        }
    }
    audio.pressPanicButton();
}  

if (testingPlayLead) {
    cout << "playing lead only "<< endl; 
    
    //audio.setMelody(melody);
   //audio.setAccompaniment(true);
    audio.setChords(true,CHORDS_123);
    //audio.setRhythm(true, RHYTHM_4_4);   
    int i = 0;
    if (piano) {
        audio.setDynamics(DYNAMICS_PIANO);
        i = 0;
        while(i < 60){
            if(melody[i] == NO_NOTE)
                audio.play(melody[i], 0, melody[i+1]); 
            else
                audio.play(melody[i], -1, melody[i+1]);    
            SLEEP(tempo);
            i += 2;
        }
        audio.pressPanicButton();
    }    
    if (pianissimo) {
        audio.setDynamics(DYNAMICS_PIANISSIMO);
        i = 0;
        while(i < 60){
            if(melody[i] == NO_NOTE)
                audio.play(melody[i], 0, melody[i+1]); 
            else
                audio.play(melody[i], -1, melody[i+1]);    
             SLEEP(tempo);
            i += 2;
        }
        audio.pressPanicButton();
    }
    if (forte) { 
        audio.setDynamics(DYNAMICS_FORTE);
        i = 0;
        while(i < 60){
            if(melody[i] == NO_NOTE)
                audio.play(melody[i], 0, melody[i+1]); 
            else
                audio.play(melody[i], -1, melody[i+1]); 
               
            SLEEP(tempo);
            i += 2;
        }
        audio.pressPanicButton();
    }
    if (fortissimo) {
        audio.setDynamics(DYNAMICS_FORTISSIMO);
        i = 0;
        while(i < 60){
            if ((i % 4) == 0)//test if melody counter is being updated correctly
                if(melody[i] == NO_NOTE)
                    audio.play(melody[i], 0, melody[i+1]); 
                else
                    audio.play(melody[i], 0, melody[i+1]);
            else 
                audio.play();    
            SLEEP(tempo);
            i += 2;
        }
    }
    audio.pressPanicButton();
}  

if (testingPlayLeadAcc) {
    cout << "playing lead and accompaniment "<< endl; 
    audio.setAccompaniment(false);
    audio.setChords(true,CHORDS_THIRD);
    audio.setRhythm(true, RHYTHM_3_4);   
    int i = 0;
    if (piano) {
        audio.setDynamics(DYNAMICS_PIANO);
        i = 0;
        while(i < 60){
            if (melody[i] != NO_NOTE) {
                audio.play(melody[i],0, melody[i+1], melody[i]-8,0, melody[i+1]);
            }
            else {
                audio.play(melody[i],0, melody[i+1], melody[i],0, melody[i+1]);   
            } 
            SLEEP(tempo);
            i += 2;
        }
    }    
    if (pianissimo) {
        audio.setDynamics(DYNAMICS_PIANISSIMO);
        i = 0;
        while(i < 60){
            if (melody[i] != NO_NOTE) {
                audio.play(melody[i],0, melody[i+1], melody[i]-8,0, melody[i+1]);
            }
            else {
                audio.play(melody[i],0, melody[i+1], melody[i],0, melody[i+1]);   
            } 
            SLEEP(tempo);
            i += 2;
        }
    }
    if (forte) { 
        audio.setDynamics(DYNAMICS_FORTE);
        i = 0;
        while(i < 60){
            if (melody[i] != NO_NOTE) {
                audio.play(melody[i],0, melody[i+1], melody[i]-8,0, melody[i+1]);
            }
            else {
                audio.play(melody[i],0, melody[i+1], melody[i],0, melody[i+1]);   
            }
            SLEEP(tempo);
            i += 2;
        }
    }
    if (fortissimo) {
        audio.setDynamics(DYNAMICS_FORTISSIMO);
        i = 0;
        while(i < 60){
            if (melody[i] != NO_NOTE) {
                audio.play(melody[i],0, melody[i+1], melody[i]-8,0, melody[i+1]);
            }
            else {
                audio.play(melody[i],0, melody[i+1], melody[i],0, melody[i+1]);   
            }    
            SLEEP(tempo);
            i += 2;
        }
    }
    audio.pressPanicButton();
}  

	return 0;
}

#endif
