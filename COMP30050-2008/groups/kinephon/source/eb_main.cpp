#ifdef __EB__

#pragma warning(disable: 4786)
#include <GL/glut.h>
#include <iostream>
#include "type.h"
#include "rai/recorder/frame.h"
#include "rai/recorder/recorder.h"

using namespace interpreter;

void display(void);
void motion(int x, int y);
void timer(int t);
Recorder g_recorder;
tick g_time = 0;

int main(int argc, char * * argv)
{

	glutInit(&argc, argv);
	glutInitWindowSize(800, 600);
	glutInitDisplayMode(GLUT_RGB | GLUT_SINGLE);

	glutCreateWindow("rai test");
	glutDisplayFunc(display);
	glutPassiveMotionFunc(motion);
	glutTimerFunc(100, timer, 0);

	g_recorder.control(econtrol::FOUND, 0);

	glutMainLoop();

	return 0;

}

void display(void)
{

	Recording * recording = g_recorder.eject();

	glClear(GL_COLOR_BUFFER_BIT);

	glBegin(GL_LINES);
	
	glVertex3i(0, 0, 0);
	glVertex3i(1, 0, 0);
	
	glEnd();

	g_recorder.erase(recording);

}

void motion(int x, int y)
{
	g_recorder.record(0, x, y, 1, g_time);
	glutPostRedisplay();
}

void timer(int t)
{
	g_time++;
}

#endif
