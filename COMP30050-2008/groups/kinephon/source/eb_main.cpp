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
#include "rai/Analyser/Math.h"
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
int recordTime = 4;

#include <vector>
using std::vector;

int main(int argc, char * * argv)
{


	vector<uchar>test(5);
	vector<vector<uchar> > test2;
	test[0] = 5;
	test[1] = 4;
	test[2] = 3;
	test[3] = 1;
	test2.push_back(test);
	cout << test.size() << endl;
	cout << test2.size() << endl;
	cout << test2[0].size() << endl;

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
	ShapesLoader::RunTest();
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

void examineShape
(	sid			shapeId,
	Points &	points
){	uint			i;
	static uint		t = 0;
	int x = t % 25;
	int y = t / 25;

	switch(shapeId)
	{
		case 100:
			glColor3f(0.0f, 1.0f, 0.0f);
			for(i = 1; i < points.length(); i++)
			{	glBegin(GL_LINES);
				glVertex3i(points[i - 1].x + x * 32, points[i - 1].y + y * 32, 0);
				glVertex3i(points[i    ].x + x * 32, points[i    ].y + y * 32, 0);
				glEnd();
			}
			t++;
			if(t >= 768)
				t = 0;
			break;
		case 0:
		case esid::TRIANGLE:
			if(shapeId == 0)
				glColor3f(0.0f, 1.0f, 0.0f);
			else
				glColor3f(0.0f, 0.0f, 1.0f);
			for(i = 1; i < points.length(); i++)
			{	glBegin(GL_LINES);
				glVertex3i(points[i - 1].x, points[i - 1].y, 0);
				glVertex3i(points[i    ].x, points[i    ].y, 0);
				glEnd();
			}
			break;
		case esid::DYNAMICS_PIANO:
			glColor3f(0.0f, 1.0f, 0.0f);
			for(i = 1; i < points.length(); i++)
			{	glBegin(GL_LINES);
				glVertex3i(points[i - 1].x - points[0].x, -points[i - 1].y + 200, 0);
				glVertex3i(points[i    ].x - points[0].x, -points[i    ].y + 200, 0);
				glEnd();
			}
			break;
		case esid::DYNAMICS_FORTE:
			glColor3f(1.0f, 0.0f, 0.0f);
			for(i = 1; i < points.length(); i++)
			{	glBegin(GL_LINES);
				glVertex3i(points[i - 1].x - points[0].x, -points[i - 1].y + 400, 0);
				glVertex3i(points[i    ].x - points[0].x, -points[i    ].y + 400, 0);
				glEnd();
			}
			break;
	}

}

void display(void)
{	uint nPoints;

	glClear(GL_COLOR_BUFFER_BIT);

	shapeEditHook = examineShape;
	ShapeMatches shapeMatches(0.75f, 1);

	Recording & recording = *g_recorder.eject();
	for(uint i = 0; i < recording.length(); i++)
	{

		nPoints = recording[i]->length();

		g_shapes->compare(recording[i], &shapeMatches);

		if(nPoints > (800u / recordTime))
			g_recorder.erase(0, nPoints - (800u / recordTime));

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

void key(unsigned char key, int, int)
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
