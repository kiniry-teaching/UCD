#!/bin/bash
(#we are in a subshell, in theory at least, and the return control
#to script
fluidsynth PC51f.sf2 -m alsa_seq &)

#and now we launch the main:
echo Please press buttons numbered 1 and 2 on your wiimote
./Kinephon
echo started
