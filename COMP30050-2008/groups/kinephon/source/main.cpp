#ifdef __KP__

#ifdef WIN32
#	pragma warning(disable: 4786)
#endif
#include <GL/glut.h>
#include <GL/gl.h>
#include <string>
#include <iostream>
#include "Python.h"
#include "Config.h"
#include "audio/Conductor.h"
#include "rai/Recorder/Recorder.h"
#include "rai/Analyser/Shapes.h"
#include "rai/Analyser/ShapesLoader.h"
#include "Parser/Parser.h"
#include "wiimote/WiimoteInterface.h"
#include "Version_Interpreter/Movement.h"
#include "Version_Interpreter/Interpreter.h"
#include "Version_Interpreter/Melody.h"
#include "type.h"
#include <sys/time.h>

using std::string;
using std::cout;
using std::endl;

using namespace audio;
using namespace interpreter;

///////////////////////////////////////////////////////////////////////////////
// globals
//
Conductor *			g_Conductor		= 0;
Recorder *			g_Recorder		= 0;
Shapes *			g_Shapes		= 0;
Parser *			g_Parser		= 0;
WiimoteInterface *	g_Wiimote		= 0;
Interpreter *		g_Interpreter	= 0;
movement *			g_Movement		= 0;							

///////////////////////////////////////////////////////////////////////////////
// prototype
//
/**
 * Process the program arguments
 * @param argc Count of arguments
 * @param argv Value of arguments
 * @returns true if OK to start kinephon or false to shutdown 
 */
bool	initializeArgs
(	int &		argc,
		char * *	argv
);
/**
 * Start all subsystems
 * @returns true if OK to start kinephon or false to shutdown 
 */
bool	initialize		(void);
/**
 * Display a modal configuration dialog box
 * @returns true if OK to start kinephon or false to shutdown 
 */
bool	displayConfig	(void);
/**
 * Run kinephon
 */
void	kinephon		(void);
/**
 * Render the visualisations
 */
void	glutOnTimer
(	int			timerId
);
/**
 * Render the visualisations
 */
void	glutOnPaint		(void);
/**
 * Respond to the keyboard
 */
void	glutOnKeyDown
(	uchar		keyCode,
		int			mouseX,
		int			mousyY
);
/**
 * Respond to window resize
 */
void	glutOnSize
(	int			width,
		int			height
);

///////////////////////////////////////////////////////////////////////////////
// main
//
/**
 * Entry point.
 * Press <Esc> or 'q' to quit
 * @param argc Count of arguments
 * @param argv Value of arguments
 * @return 0 if the program ran successfully, else 1
 */
int main(int argc, char * * argv)
{

	if(initializeArgs(argc, argv) == true
			&& initialize() == true)
		glutMainLoop();
	else
		return 1;

	return 0;

}

///////////////////////////////////////////////////////////////////////////////
// kinephon stuff - called once every beat (g_BMP)
//
void kinephon(void)
{	uint			index;
ShapeMatches	shapeMatches(0.75f, 1);

g_Wiimote->feedReport();

Recording & recording = *g_Recorder->eject();
for(index = 0; index < recording.length(); index++)
{

	g_Shapes->compare(recording[index], &shapeMatches);

	g_Interpreter->shapeMatching(&shapeMatches);
	g_Movement->audioMovement(recording[index]);

	// Perform some cleanup, just force to 100 frames max for now
	g_Recorder->erase
	(	recording[index]->iid(),
			recording[index]->length() - 100
	);

}

g_Recorder->erase(&recording);

timeval temp; 
gettimeofday(&temp, NULL);

//cout << "timer in main: difference " << (temp.tv_sec*1000+(temp.tv_usec /1000)) - (timer.tv_sec*1000+(timer.tv_usec /1000));

if ((uint)(temp.tv_sec*1000+(temp.tv_usec /1000)) - (uint)(timer.tv_sec*1000+(timer.tv_usec /1000)) >= 200)
{
	//	cout<< "timer in main " << (temp.tv_sec*1000+(temp.tv_usec /1000))<<endl;
	timer = temp;

	g_Conductor->play();
}


}

///////////////////////////////////////////////////////////////////////////////
// intialise command line
//
bool initializeArgs
(	int &		argc,
		char * *	argv
){	int			index;
string		arg;
bool		startup	= true;

glutInit(&argc, argv);

for(index = 0; index < argc; index++)
{	arg.assign(argv[index]);
if(arg == "--config")
	Config::displayConfig = true;
else
	if(arg == "--path")
		if(index + 1 < argc)
			Config::configPath = argv[index + 1];
		else
		{	Config::showUsage = true;
		startup = false;
		}
	else
		if(arg == "--help")
			Config::showUsage = true;

}

if(startup == true)
	if(Config::displayConfig == true)
		startup = displayConfig();

if(Config::showUsage == true)
{	cout << "Usage:" << endl;
cout << " kinephon [--config] [--path <filename>] [--help]" << endl;
cout << endl;
cout << " --config  Display the configuration dialog" << endl;
cout << " --path    Change path of configuration file" << endl;
cout << " --help    Show this message" << endl;
}

return startup;

}

///////////////////////////////////////////////////////////////////////////////
// intialise kinephon
//
bool initialize(void)
{	int		retry	= 0;
bool	startup	= true;

// Start sub systems in order of output -> input
g_Conductor = new Conductor();
if(g_Conductor->initialize
		(	Config::recordMidi,
				Config::midiPort
		) == false)
	startup = false;
//cout << "conductor initialised" << endl;
//if (startup == false) {cout << "false" << endl;} else {cout << "continuing with startup" << endl;}

if(startup != false)
{	g_Interpreter = new Interpreter();
g_Movement = new movement(g_Conductor);
Melody::intialised();
}
//cout << "interpreter initialised" << endl;
//if (startup == false) {cout << "false" << endl;} else {cout << "continuing with startup" << endl;}

if(startup != false)
{

	g_Recorder = new Recorder();
	g_Shapes = ShapesLoader::loadShapes(Config::shapesPath.c_str());
	if(g_Shapes == 0)
		startup = false;

}
//cout << "recorder initialised" << endl;
//if (startup == false) {cout << "false" << endl;} else {cout << "continuing with startup" << endl;}

if(startup != false)
	g_Parser = new Parser(g_Recorder);
//cout << "parser initialised" << endl;
//if (startup == false) {cout << "false" << endl;} else {cout << "continuing with startup" << endl;}

if(startup != false)
	//	system("ls");
	//system("pwd");
	g_Wiimote = new WiimoteInterface(g_Parser);

//cout << "interface initialised" << endl;
//if (startup == false) {cout << "false" << endl;} else {cout << "continuing with startup" << endl;}
if(startup != false)
	for(retry = 0; retry < 4; retry++)
	{

		//			Config::wiimote = g_Wiimote->findWiimote();

		if(Config::wiimote != WiimoteInterface::NOT_FOUND)
			retry = 5;

	}

if(retry == 4)
	startup = false;

//cout << "wiimote search complete (init)" << endl;
//if (startup == false) {cout << "false" << endl;} else {cout << "continuing with startup" << endl;}
if(startup != false)
	g_Wiimote->connectTo(Config::wiimote);

cout << "connected to wiimote" << endl;
//if (startup == false) {cout << "false" << endl;} else {cout << "continuing with startup" << endl;}
// Start glut
if(startup != false)
{

	// Set window properties
	glutInitWindowSize(800, 600);
	glutInitDisplayMode(GLUT_RGB | GLUT_DOUBLE);
	// Set callbacks
	glutCreateWindow("kinephon");
	glutDisplayFunc(glutOnPaint);
	glutIdleFunc(glutOnPaint);
	glutKeyboardFunc(glutOnKeyDown);
	glutReshapeFunc(glutOnSize);
	glutFullScreen();
	// Set render properties
	glDisable(GL_DEPTH_TEST);
	glClear(GL_COLOR_BUFFER_BIT);

}

//cout << "glut started" << endl;
//if (startup == false) {cout << "false" << endl;} else {cout << "continuing with startup" << endl;}

if(startup == false)
{	ShapesLoader::unloadShapes(g_Shapes);
delete g_Recorder;
delete g_Conductor;
}

return startup;

}

///////////////////////////////////////////////////////////////////////////////
// configuration dialog
//
bool displayConfig(void)
{

	// @todo - Display configuration dialog

	return true;

}

///////////////////////////////////////////////////////////////////////////////
// glut stuff
//
void glutOnPaint(void)
{

	kinephon();

	glClear(GL_COLOR_BUFFER_BIT);

	//	glBegin(GL_LINES);
	//	for(Frame* frame = recording[index]->first(); frame != 0 && frame->next() != 0; frame = frame ->next())
	//	{
	//		glVertex2i(frame->y(), frame->y());
	//		glVertex2i(frame->next()->x(), frame->next()->y());		
	//	}
	//	glEnd();

	glutSwapBuffers();

}

void glutOnKeyDown
(	uchar	keyCode,
		int,
		int
){

	if(keyCode == 27
			|| keyCode == 'q')
		exit(0);

}

/**
 * Respond to window resize
 */
void glutOnSize
(	int			width,
		int			height
){

	// Set display properties
	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	glOrtho(0, width, height, 0, 0, 1);
	glMatrixMode(GL_MODELVIEW);

}

#endif
