#ifndef BLIMP2_H_
#define BLIMP2_H_
#include "linklist.h"
class Blimp2
{
public:
	Blimp2();
    void getCurrpos();
    float getCurrX();
    float getCurrY();
    float getCurrZ();
    float readDesX();
    float readDesY();
    float readDesZ();
    float getVelocityx();
    float getVelocityy();
    float getDistance(float, float, float, float);
    void Navigate();
	virtual ~Blimp2();
private:
	float desX, desY, desZ, radius, currX, currY, currZ;
	bool servo1,servo2,motor1,motor2;
	int timer;
	linklist past;
	
};

#endif /*BLIMP2_H_*/
