#ifndef AUDIOCONTROLLER_H_
#define AUDIOCONTROLLER_H_

#include "Channel.h"
#include "RtMidi.h"
#include <string>
using namespace std;

/*
 * Author:	ED
 *
 * Interface for audio creation that is in charge of all audio
 * operations.
 * 
 */

class AudioController
{
public:
	//Create a new AudioController
	AudioController();
	//TODO: check that we have destroyed everything...
	virtual ~AudioController();

	//open a new channel (maybe return it's number)
	int openChannel();

	//adjusts how channels are managed among themselves
	char getChannelMode();
	void setChannelMode();
	
	//adjust each channel's setting separately
	char getControlChange(int channelNo, string whatever);
	void setControlChange(int channelNo, string whatever);

	//send a message with given content
	void sendMessage(string someInput);
	
	
private:
	vector<Channel> channels;	
};

#endif /*AUDIOCONTROLLER_H_*/
