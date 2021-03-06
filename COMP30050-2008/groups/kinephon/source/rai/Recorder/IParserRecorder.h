#ifndef __INTERPRETER_PARSERRECORDER_H__
#define __INTERPRETER_PARSERRECORDER_H__

#include "../../type.h"

namespace interpreter
{

/**
 * List of control switches for IParserRecorder::control()
 * @author EB
 * @version 1.0
 */
namespace econtrol
{
	/**
	 * A new IR blob has been found by the parser. iid should contain the
	 *	id of the blob that will be used when calling Record for that blob.
	 *	Return value will always be 0
	 * @author EB
	 * @version 1.0
	 */
	ect const	FOUND	= 0;
	/**
	 * An IR blob has been lost, either because it was physically removed, or
	 *	because it's data packets have been lost. iid should contain the
	 *	id of the blob lost
	 *	Return value will always be 0
	 * @author EB
	 * @version 1.0
	 */
	ect const	LOST	= 1;
	/**
	 * The Parser is no longer receiving data. Connection may be lost. iid is
	 *	ignored and can be any value
	 *	Return value will always be 0
	 * @author EB
	 * @version 1.0
	 */
	ect const	BADCOM	= 2;
}

/**
 * Interface between Parser and Recorder.
 * The parser will call on the methods availabe
 *	here and the Recorder will respond to them.
 * @author EB
 * @version 1.0
 */
class IParserRecorder
{

public:
	/**
	 * Issue a control switch.
	 * Used to add or remove IR blob ids, or indicate errors
	 * @param control Control switch to make. Values are enumerated in econtrol
	 * @param iid If the control requires the IRId, it is passed here. Each
	 *	control will specify whether it needs this data
	 * @return If the control needs to respond, it will be returned here. Each
	 *	control will specify what is returned.
	 * @see econtrol
	 */
	virtual int		control
					(	ect const		control,
						irid const		iid
					)					pure;
	/**
	 * Record the current position of an IR blob.
	 * @param iid Identification of the IR blob. This id will be used to link
	 *	each Record together
	 * @param x X co-ordinate of the IR blob
	 * @param y Y co-ordinate of the IR blob
	 * @param size Size of the IR blob
	 * @param time The time this record happened
	 * @author EB
	 * @version 1.0
	 * @post id must be added by calling Control
	 * @pre size > 0;
	 */
	virtual void	record
					(	irid const		iid,
						short const		x,
						short const		y,
						short const		size,
						tick const		time
					)					pure;

};

}

#endif
