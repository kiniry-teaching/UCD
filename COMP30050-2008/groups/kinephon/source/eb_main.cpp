#ifdef __EB__

#ifdef WIN32
#	pragma warning(disable: 4786)
#endif
#include <GL/glut.h>
#include <iostream>
#include <cmath>
#include <stdio.h>
#include "rai/TestMemory.h"
#include "type.h"
#include "rai/Analyser/ShapeMatches.h"
#include "rai/Analyser/Shapes.h"
#include "rai/Analyser/ShapesLoader.h"
#include "rai/Recorder/Frame.h"
#include "rai/Recorder/Track.h"
#include "rai/Recorder/Recorder.h"
#include "rai/ShapeId.h"

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
int speedDelay = 4;
int accelDelay = 10;
int recordTime = 10;

int main(int argc, char * * argv)
{

#ifdef __TEST__

	// Dump memory report twice to stabilise the latent memory use
	//	After each test is run, the memory dump memory usage should
	//	match the value of the second dump here, if the test didn't
	//	introduce memory leaks
	dumpMemoryReport();
	dumpMemoryReport();
	Frame::RunTest();
	Track::RunTest();
	Recorder::RunTest();
	Zone::RunTest();
//	ShapesLoader::RunTest();
	ShapeMatches::RunTest();

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

void ExamineShape
(	sid const	shapeId,
	int * const	points,
	uint const	nPoints
){	uint		i;

	switch(shapeId)
	{
		case esid::TRIANGLE:
			glColor3f(0.0f, 0.0f, 1.0f);
			for(i = 2; i < nPoints; i += 2)
			{	glBegin(GL_LINES);
				glVertex3i(points[i - 2], points[i - 1], 0);
				glVertex3i(points[i], points[i + 1], 0);
				glEnd();
			}
			break;
		case esid::DYNAMICS_PIANO:
			glColor3f(0.0f, 1.0f, 0.0f);
			for(i = 2; i < nPoints; i += 2)
			{	glBegin(GL_LINES);
				glVertex3i(points[i - 2] - points[0], -points[i - 1] + 100, 0);
				glVertex3i(points[i] - points[0], -points[i + 1] + 100, 0);
				glEnd();
			}
			break;
		case esid::DYNAMICS_FORTE:
			glColor3f(1.0f, 0.0f, 0.0f);
			for(i = 2; i < nPoints; i += 2)
			{	glBegin(GL_LINES);
				glVertex3i(points[i - 2] - points[0], -points[i - 1] + 400, 0);
				glVertex3i(points[i] - points[0], -points[i + 1] + 400, 0);
				glEnd();
			}
			break;
	}

}

void display(void)
{	uint nPoints;

	glClear(GL_COLOR_BUFFER_BIT);

	shapeEditHook = ExamineShape;
	ShapeMatches shapeMatches(0.75f, 1);

	Recording & recording = *g_recorder.eject();
	for(uint i = 0; i < recording.length(); i++)
	{

		nPoints = recording[i]->length();

		g_shapes->compare(recording[i], &shapeMatches);

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
