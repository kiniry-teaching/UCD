#ifdef __EB__

#pragma warning(disable: 4786)
#include <GL/glut.h>
#include <iostream>
#include "type.h"
#include "rai/analyser/shapes.h"
#include "rai/analyser/shapesloader.h"
#include "rai/recorder/frame.h"
#include "rai/recorder/recorder.h"

using namespace interpreter;

void display(void);
void motion(int x, int y);
void timer(int t);
void entry(int state);
Shapes * g_shapes;
Recorder g_recorder;
tick g_time = 0;

int tx = -1, ty = 0;
int lx = 0, ly = 0;

int main(int argc, char * * argv)
{

	glutInit(&argc, argv);
	glutInitWindowSize(800, 600);
	glutInitDisplayMode(GLUT_RGB | GLUT_SINGLE);

	glutCreateWindow("rai test");
	glutDisplayFunc(display);
	glutPassiveMotionFunc(motion);
	glutTimerFunc(100, timer, 0);
	glutTimerFunc(1231, timer, 1);
	glutEntryFunc(entry);

	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	glOrtho(0, 800, 600, 0, 0, 1);
	glMatrixMode(GL_MODELVIEW);

	glDisable(GL_DEPTH_TEST);
	glClear(GL_COLOR_BUFFER_BIT);

	g_recorder.control(econtrol::FOUND, 0);

	g_shapes = ShapesLoader::loadShapes("C:\\Data\\College\\COMP30050 - Software Engerineering Project III\\kinephon\\source\\rai\\kinephon.sec");

	glutMainLoop();

	return 0;

}

void display(void)
{

	Recording * recording = g_recorder.eject();

	glClear(GL_COLOR_BUFFER_BIT);

	glBegin(GL_LINES);
	
	glVertex3i(lx, ly, 0);
	glVertex3i(tx, ty, 0);
	
	glEnd();

	glFlush();

	g_recorder.erase(recording);

}

void motion(int x, int y)
{
	g_recorder.record(0, x, y, 1, g_time);
}

void entry(int state)
{

	tx = -1;

}

void timer(int t)
{

	if(t == 0)
		g_time++;
	else
		glutPostRedisplay();
		
}

#endif
