#ifdef __EB__

#pragma warning(disable: 4786)
#include <GL/glut.h>
#include <iostream>
#include "type.h"
#include "rai/analyser/Shapes.h"
#include "rai/analyser/ShapesLoader.h"
#include "rai/recorder/Frame.h"
#include "rai/recorder/Track.h"
#include "rai/recorder/Recorder.h"

using namespace interpreter;

void display(void);
void motion(int x, int y);
void timer(int t);
void entry(int state);
Shapes * g_shapes;
Recorder g_recorder;
tick g_time = 0;
int mx = 0;
int my = 0;

int main(int argc, char * * argv)
{

#ifdef __TEST__

	Frame::RunTest();
	Track::RunTest();
	Recorder::RunTest();

#else

	glutInit(&argc, argv);
	glutInitWindowSize(800, 600);
	glutInitDisplayMode(GLUT_RGB | GLUT_SINGLE);

	glutCreateWindow("rai test");
	glutDisplayFunc(display);
	glutPassiveMotionFunc(motion);
	glutTimerFunc(10, timer, 0);
	glutTimerFunc(1231, timer, 1);

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

		glColor3f(0.5f * m, 0.0f, 0.0f);
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

	if(nPoints <= 1)
		return;

	glColor3f(0.0f, 1.0f, 0.0f);
	glBegin(GL_LINES);

	for
	(	frame = track.first();
		frame->next() != 0;
		frame = frame->next()
	){

		x = frame->time();
		y = ((frame->u() << 1) + (frame->v() << 1));
		if(y < 0) y = -y;
		y = 400 - y;

		if(lx == 0)
		{	sx = lx = x;
			ly = y;
		}

		glVertex3i(lx - sx, ly, 0);
		glVertex3i(x - sx, y, 0);
		lx = x;
		ly = y;

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
	int ya;
	int yb;

	if(nPoints <= 2)
		return;

	glColor3f(0.0f, 0.0f, 1.0f);
	glBegin(GL_LINES);

	for
	(	frameLast = track.first(),
		frame = frameLast->next();
		frame->next() != 0;
		frameLast = frame,
		frame = frame->next()
	){

		x = frame->time();
		ya = (frame->u() << 1) + (frame->v() << 1);
		yb = (frameLast->u() << 1) + (frameLast->v() << 1);
		if(ya < 0) ya = -ya;
		if(yb < 0) yb = -yb;
		y = ya - yb;
		y += 200;
//		x *= 5;
//		y *= 2;

		if(lx == 0)
		{	sx = lx = x;
			ly = y;
		}

		glVertex3i(lx - sx, ly, 0);
		glVertex3i(x - sx, y, 0);
		lx = x;
		ly = y;

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

		if(nPoints > 640)
			g_recorder.erase(0, nPoints - 640);

	}

	g_recorder.erase(&recording);

	glFlush();

}

void motion(int x, int y)
{
	mx = x;
	my = y;
}

void timer(int t)
{

	if(t == 0)
	{	g_time++;
		g_recorder.record(0, mx, my, 1, g_time);
		glutPostRedisplay();
		glutTimerFunc(10, timer, 0);
	}
	else
	{	glutPostRedisplay();
//		glutTimerFunc(1231, timer, 1);
	}

}

#endif
