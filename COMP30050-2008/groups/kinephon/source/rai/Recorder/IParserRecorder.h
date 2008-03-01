#ifndef __INTERPRETER_PARSERRECORDER_H__
#define __INTERPRETER_PARSERRECORDER_H__

namespace interpreter
{

/**
 * List of control switches for IParserRecorder::Control(int, void*)
 * @author EB
 * @version 1.0
 */
namespace control
{
	/**
	 * A new IR blob has been found by the parser. /v data should contain the
	 *	id of the blob that will be used when calling Record for that blob.
	 *	Return value will always be 0
	 * @author EB
	 * @version 1.0
	 */
	int const	FOUND	= 0;
	/**
	 * An IR blob has been lost, either because it was physically removed, or
	 *	because it's data packets have been lost. /v data should contain the id
	 *	of the blob lost
	 *	Return value will always be 0
	 * @author EB
	 * @version 1.0
	 */
	int const	LOST	= 1;
	/**
	 * The Parser is no longer receiving data. Connection may be lost. /v data
	 *	is ignored
	 *	Return value will always be 0
	 * @author EB
	 * @version 1.0
	 */
	int const	BADCOM	= 2;
}

/**
 * Interface between Parser and Recorder.
 * The parser will call on the methods availabe
 *	here to and the Recorder will capture them.
 * @author EB
 * @version 1.0
 */
class IParserRecorder
{

public:
	/**
	 * Issue a control switch.
	 * Used to add or remove IR blob ids, indicate errors
	 * @param control Control switch to make.
	 * @param data If the control requires extra data, it is passed here. Each
	 *	control will specify the type of data to pass
	 * @return If the control needs to respond, it will be returned here. Each
	 *	control will specify what is returned
	 */
	virtual int		Control
					(	int const	control,
						void *		data
					)	pure;

	/**
	 * Record the current position of an IR blob.
	 * @param id Identification of the IR blob. This id will be used to link
	 *	each Record together
	 * @param x X co-ordinate of the IR blob
	 * @param y Y co-ordinate of the IR blob
	 * @param size Size of the IR blob
	 * @author EB
	 * @version 1.0
	 * @post id must be added by calling Control
	 * @pre size > 0;
	 */
	virtual void	Record
					(	int const	id,
						int const	x,
						int const	y,
						int const	size
					)	pure;

};

}

#endif
