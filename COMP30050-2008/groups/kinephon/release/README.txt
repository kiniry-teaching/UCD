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
# INSTALLATION:
##################################
1.) Make sure you have the following packages installed:
- python, at least version 2.4
- pybluez
- fluidsynth (you will require ALSA sound library for this, but this usually comes with a Linux distribution)

2.) Open a Terminal and run the (...) script. Leave this window open, since it will run the software synthesizer which is needed
	for the entire runtime of the application.

##################################
# TROUBLESHOOTING:
##################################
* I can hear no sound.
--> Check if your sound is not muted. It may also be that the sound is muted inside the soundlibrary ALSA. For checking this run
	alsamixer in a terminal window and adjust the settings accordingly.
--> Check if your terminal window in which you ran the script is still open. If it is, check that fluidsynth is still working and does not give any other
	error messages than something like 'lost events' (you can safely ignore those).
--> 




