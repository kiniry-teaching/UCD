Audio - 
provides a set of classes that take essential 
information about the sound to be produced and converts it
into Midi messages which are then sent to an available Midi-port.

ESSENTIAL NOTES:
Due to the fact that common on-board sound cards do not have direct
Midi support we will use a software synthesizer and a soundfont file 
for Linux. In Windows, the synthesizer is already built in, we will 
see later in what extent we can use it. All following instructions 
are for a Linux OS.

MIDI INSTRUCTIONS:
As for now (we might try to simplify this in the future):
1.) install the command-line synthesizer "fluidsynth". (You can do this
	via the Synaptic Package Manager). 
2.) download the soundfont "PC51f.sf2" and place it in some directory 
	you'll find later.
3.) start fluidsynth in a terminal window, by typing:
	$ fluidsynth <path-to-soundfont>PC51f.sf2 -m alsa_seq -a alsa
	(Don't worry about any error messages, as long as it says in 
	 	 the end it's laoded...)
	IMPORTANT: DON'T CLOSE THIS TERMINAL WINDOW UNTIL FINISHED WITH
				ANY MIDI OUTPUT!
				
COMPILING INSTUCTIONS:
Since the RTMidi code is portable, we need to specify what OS we are
running (maybe will be automatic in the future), as for now:
1.) The code for main() will be commented out, otherwise if you had 
	two main()s in the project it wouldn't compile. If you want to have 
	a go at the audio part, comment out any other main() and uncomment
	the main in midiout.cpp.

2.)
- In Eclipse: Go to Project -> Properties
	in the pop-up window navigate to:
	C/C++ Build, GCC C++ Compiler, Preprocessor
	Click on the green "+" button under 'Defined symbols' and
	type: __LINUX_ALSASEQ__  (that's 2 underscores at front and back).
	
- not in Eclipse: Make sure you specify somewhere the preprocessor 
	definition: -D__LINUX_ALSASEQ__
	
3.)
- In Eclipse: Go to Project -> Properties
	in the pop-up window navigate to:
	C/C++ Build, GCC C++ Linker, Libraries
	Click on the green "+" button under 'Libraries' and add
	'asound' and 'pthread'
	
- not in Eclipse: Make sure you specify somewhere the libraries:
	-lasound -lpthread
	
RUNNING DEMO:
If all the setup and compilation was successful, running the program
will ask you:
"Would you like to open a virtual output port? [y/N]" 	
 	--> type 'N'

You'll see a list of possible output ports, numbered #0, #1 etc.
"Choose a port number:"
	--> type in a number. If you don't hear anything try another, 
		at least one of the port should give you a sign of life...