#ifdef __EB__

#ifdef WIN32
#	pragma warning(disable: 4786)
#endif
#include <GL/glut.h>
#include <iostream>
#include <cmath>
#include "type.h"
#include "rai/Analyser/Shapes.h"
#include "rai/Analyser/ShapesLoader.h"
#include "rai/Recorder/Frame.h"
#include "rai/Recorder/Track.h"
#include "rai/Recorder/Recorder.h"

using namespace interpreter;

void display(void);
void motion(int x, int y);
void timer(int t);
void entry(int state);
void key(unsigned char key, int x, int y);
Shapes * g_shapes;
Recorder g_recorder;
tick g_time = 0;
int mx = 0;
int my = 0;
int speedDelay = 10;
int accelDelay = 2;
int recordTime = 1;

int main(int argc, char * * argv)
{

#ifdef __TEST__

	Frame::RunTest();
	Track::RunTest();
	Recorder::RunTest();

#else

	glutInit(&argc, argv);
	glutInitWindowSize(800, 600);
	glutInitDisplayMode(GLUT_RGB | GLUT_DOUBLE);

	glutCreateWindow("rai test");
	glutDisplayFunc(display);
	glutPassiveMotionFunc(motion);
	glutTimerFunc(10, timer, 0);
	glutTimerFunc(1231, timer, 1);
	glutKeyboardFunc(key);

	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	glOrtho(0, 800, 600, 0, 0, 1);
	glMatrixMode(GL_MODELVIEW);

	glDisable(GL_DEPTH_TEST);
	glClear(GL_COLOR_BUFFER_BIT);

	g_recorder.control(econtrol::FOUND, 0);

	g_shapes = ShapesLoader::loadShapes("C:\\Data\\College\\COMP30050 - Software Engerineering Project III\\kinephon\\source\\rai\\kinephon.sec");

	glutMainLoop();

#endif

	return 0;

}

void displayMovement(Track const & track, uint nPoints)
{	Frame * frame;
	int	lx;
	int ly;
	int m = 2;

	if(nPoints <= 0)
		return;

	glBegin(GL_LINES);

	for
	(	frame = track.first(), lx = frame->x(), ly = frame->y();
		frame->next() != 0;
		frame = frame->next()
	){

		glColor3f(0.0f, 0.0f, 0.5f * m);
		m = (m == 2 ? 1 : 2);

		glVertex3i(lx, ly, 0);
		glVertex3i(frame->x(), frame->y(), 0);
		lx = frame->x();
		ly = frame->y();

	}

	glEnd();

}

void displaySpeed(Track const & track, uint nPoints)
{	Frame * frame;
	int sx;
	int	lx = 0;
	int ly;
	int x;
	int y;

	Frame * frameDelay;
	Frame * frameSmooth;
	int ySmooth;
	int lySmooth;
	int delay = 0;
	int smooth;

	if(nPoints <= 1)
		return;

	glBegin(GL_LINES);

	for
	(	frameDelay = frame = track.first();
		frame->next() != 0;
		frame = frame->next()
	){

		x = frame->time();
		y = (int)(sqrt(abs((frame->u() << 1) + (frame->v() << 1))) * 10);
		y = 400 - y;

		if(delay < speedDelay)
			delay++;
		else
			frameDelay = frameDelay->next();

		for
		(	smooth = 0,
			frameSmooth = frameDelay,
			ySmooth = 0;
			smooth < (delay << 1)
		 && frameSmooth != 0;
			smooth++,
			frameSmooth = frameSmooth->next()
		)	ySmooth += (int)(sqrt(abs((frameSmooth->u() << 1) + (frameSmooth->v() << 1))) * 10);
		
		ySmooth /= smooth;
		ySmooth = 400 - ySmooth;

		if(lx == 0)
		{	sx = lx = x;
			ly = y;
			lySmooth = ySmooth;
		}

		glColor3f(0.0f, 0.25f, 0.0f);
		glVertex3i(lx - sx, ly, 0);
		glVertex3i(x - sx, y, 0);

		glColor3f(0.0f, 1.0f, 0.0f);
		glVertex3i(lx - sx, lySmooth, 0);
		glVertex3i(x - sx, ySmooth, 0);

		lx = x;
		ly = y;
		lySmooth = ySmooth;

	}

	glEnd();

}

void displayAccel(Track const & track, uint nPoints)
{	Frame * frame;
	Frame * frameLast;
	int sx;
	int	lx = 0;
	int ly;
	int x;
	int y;

	Frame * frameDelay;
	Frame * frameSmooth;
	Frame * frameSmoothLast;
	int ySmooth;
	int lySmooth;
	int delay = 0;
	int smooth;

	if(nPoints <= 2)
		return;

	glBegin(GL_LINES);

	delay = 0;
	for
	(	frameDelay = frameLast = track.first(),
		frame = frameLast->next();
		frame->next() != 0;
		frameLast = frame,
		frame = frame->next()
	){

		x = frame->time();
		y = (int)((sqrt(abs((frame->u() << 1) + (frame->v() << 1))) - sqrt(abs((frameLast->u() << 1) + (frameLast->v() << 1)))) * 20);
		y += 200;

		if(delay < accelDelay)
			delay++;
		else
			frameDelay = frameDelay->next();

		for
		(	smooth = 0,
			frameSmoothLast = frameDelay,
			frameSmooth = frameDelay->next(),
			ySmooth = 0;
			smooth < (delay << 1)
		 && frameSmooth->next() != 0;
			smooth++,
			frameSmoothLast = frameSmooth,
			frameSmooth = frameSmooth->next()
		)	ySmooth += (int)((sqrt(abs((frameSmooth->u() << 1) + (frameSmooth->v() << 1))) - sqrt(abs((frameSmoothLast->u() << 1) + (frameSmoothLast->v() << 1)))) * 80);

		ySmooth /= smooth;
		ySmooth += 200;

		if(lx == 0)
		{	sx = lx = x;
			ly = y;
			lySmooth = ySmooth;
		}

		glColor3f(0.25f, 0.0f, 0.0f);
		glVertex3i(lx - sx, ly, 0);
		glVertex3i(x - sx, y, 0);

		glColor3f(1.0f, 0.0f, 0.0f);
		glVertex3i(lx - sx, lySmooth, 0);
		glVertex3i(x - sx, ySmooth, 0);

		lx = x;
		ly = y;
		lySmooth = ySmooth;

	}

	glEnd();

}

void display(void)
{	uint nPoints;

	glClear(GL_COLOR_BUFFER_BIT);

	Recording & recording = *g_recorder.eject();
	for(uint i = 0; i < recording.length(); i++)
	{

		nPoints = recording[i]->length();

		displayMovement(*recording[i], nPoints);
		displaySpeed(*recording[i], nPoints);
		displayAccel(*recording[i], nPoints);

		if(nPoints > (800 / recordTime))
			g_recorder.erase(0, nPoints - (800 / recordTime));

	}

	g_recorder.erase(&recording);

    glutSwapBuffers();

}

void motion(int x, int y)
{
	mx = x;
	my = y;
}

void timer(int t)
{

	if(t == 0)
	{	g_time += recordTime;
		g_recorder.record(0, mx, my, 1, g_time);
		glutPostRedisplay();
		glutTimerFunc(10, timer, 0);
	}
	else
	{	glutPostRedisplay();
//		glutTimerFunc(1231, timer, 1);
	}

}

void key(unsigned char key, int x, int y)
{

	switch(key)
	{
		case '=':	speedDelay++;	break;
		case '-':	speedDelay--;	break;
		case ']':	accelDelay++;	break;
		case '[':	accelDelay--;	break;
		case '2':	recordTime++;	break;
		case '1':	recordTime--;	break;
	}

	if(speedDelay < 1)
		speedDelay = 1;
	if(accelDelay < 1)
		accelDelay = 1;
	if(recordTime < 1)
		recordTime = 1;

}

#endif
