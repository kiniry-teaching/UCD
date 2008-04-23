#ifndef __CONFIG_H__
#define __CONFIG_H__
#include <string>

using std::string;

class Config
{

///////////////////////////////////////////////////////////////////////////////
// queries - set by command line
//
public:
	/**
	 * Should the configuration dialog be displayed
	 */
	static bool		displayConfig;
	/**
	 * Path to configuration settings
	 */
	static string	configPath;
	/**
	 * Display the usage details
	 */
	static bool		showUsage;

///////////////////////////////////////////////////////////////////////////////
// queries - set by configuration file
//
public:
	/**
	 * should midi output be recorded
	 */
	static bool		recordMidi;
	/**
	 * audio midi port to open
	 */
	static string	midiPort;
	/**
	 * Path to kinephon.sec
	 */
	static string	shapesPath;
	/**
	 * 
	 */
	static string	wiimote;

///////////////////////////////////////////////////////////////////////////////
// commands
//
public:
	static bool		load			(void);

};

///////////////////////////////////////////////////////////////////////////////

inline bool Config::load(void)
{

	// TODO - read configuration file <var>configPath</var>

	// Assuming file was read OK
	return true;

}

#endif
