Project Kinephon 

30050 Software Engineering Project III - 2008

Team:		Intuitive Aptitudes
Authors:	
Sumbo Ajisafe	05005451
David Swords	05477689
Eliott Bartley	05806500
Jakub Dostal	05844151
Eva Darulova	05817625


##################################
# OVERVIEW:
##################################
In the creation of dance music, a musician has numerous theories, techniques, instruments, and hardware and software to avail of. 
Music created in this manner appears to entice people into dance. However, dance does not have to be the response to music, 
nor music a product of impassive instruments; it may well be the other way round: music should be the manifestation of dance. 
This project aims to show that one does not have to follow the old paths. With the help of software and IR cameras it will follow 
the users movements and produce music that is not stifled by any boundaries arising by having the music first.
Kinephon is a tool designed to realise movement as a audio composition. This is achieved by having the user wear IR lights. These 
IR lights are tracked by a Wiimote and spatial information is transmitted to a Bluetooth enabled device for interpretation. 
The Kinephon software uses this data to build an animation of the movement and map those movements to audible samples,
synths, or effects, thereby producing the movement's song. To enhance the use of the tool, the created data can be recorded, 
so that one can review and compare it later, maybe to the audio samples of other users.

##################################
# RUN KINEPHON:
##################################
(Note: This project has been compiled and run on Ubuntu 7.10.)
1.) Make sure you have the following packages installed:
- python, at least version 2.4
- pybluez
- fluidsynth (you will require ALSA sound library for this, but this usually comes with a Linux distribution)

2.) Open a Terminal and navigate to the release folder of the Kinephon project. Run ./Kinephon_startup. Leave this window open, 
	since it will run the software synthesizer which is needed for the entire runtime of the application.

3.) >>>>>>>>>>>IMPORTANT!!!!!<<<<<<<<<<<<<<<<<
	Before startup you need to press buttons 1 and 2 on your Wiimote and hold them during the entire startup. Otherwise the Wiimote cannot be found and the application
	will not work.

4.) In order to enable recording, you need to recompile the project.
	For this change the Config::recordMidi in the Config.cpp file to true and recompile.
	For compiling instructions, see below. 
	
##################################
# COMPILING:
##################################
You will need to include the following settings for your g++ compiler:
 -I/usr/include/python2.5 
 -D__KP__ 
 -D__LINUX_ALSASEQ__ 
-lasound
-lpthread
-glut
-GLU
-GL
-python2.5 (or your current version)

In addition to this you will also need the following packages installed:
-python-all-dev
-libbluetooth-dev

##################################
# TROUBLESHOOTING:
##################################
* I can hear no sound.
--> Check if your sound is not muted. It may also be that the sound is muted inside the soundlibrary ALSA. For checking this run
	alsamixer in a terminal window and adjust the settings accordingly.
--> Check if your terminal window in which you ran the script is still open. If it is, check that fluidsynth is still working and does not give any other
	error messages than something like 'lost events' (you can safely ignore those).

* The application does not startup properly even after a couple of minutes.
--> Make sure you are pressing the buttons 1 and 2 on your Wiimote. It is essential that you do this BEFORE and DURING the whole startup. 
--> If the Wiimote has not been found for more than 4 times, it will not startup. You need to restart your system.
--> If the application crashes and you see the error statements including python or connection it is likely that you have not been holding
 	the buttons on the Wiimote properly. 




