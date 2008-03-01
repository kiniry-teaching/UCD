#ifndef __INTERPRETER_RECORDER_H__
#define __INTERPRETER_RECORDER_H__

#include "IParserRecorder.h"

namespace interpreter
{

/**
 * Interface between Parser and Recorder.
 * The parser will call on the methods availabe
 *	here to and the Recorder will capture them.
 * @author EB
 * @version 1.0
 */
class Recorder : public IParserRecorder
{

public:
	/**
	 * Create an instance of a recorder.
	 * The recorder does nothing itself, it should be passed on to the Parser,
	 *	which will call the recorder, giving it information to record
	 * @author EB
	 * @version 1.0
	 */
					Recorder		(void);
	/**
	 * Destroy this instance of the recorder.
	 * @author EB
	 * @version 1.0
	 * @warning Destructor is not virtual, don't inherit from this class
	 */
					~Recorder		(void);

public:
	/**
	 * Eject the recording from the Recorder.
	 * Takes a copy of the recorded track up to this point. The Recorder
	 *	will still contain this copied data, so calling Eject again will
	 *	return the same track data, possibly with new frames add at the
	 *	end. To remove consumed frames from an track, call Erase.
	 * @return A copy of the recording at this point in time
	 * @author EB
	 * @version 1.0
	 */
	Recording *		Eject			(void)	const;
	/**
	 * Erase frames from an track.
	 * All frames before and including the specified frame are removed from
	 *	the track that is recording the speicified IR blob
	 * @param irid IR blob whose track is to be erased
	 * @param frame All frames from this and before are removed from the
	 *	track. If frame is -1 (default), the whole track is erased
	 * @author EB
	 * @version 1.0
	 */
	void			Erase
					(	irid const	irid,
						int const	frame	= -1
					);

public:
	/** . @copydoc IParserRecorder::Control */
	virtual int		Control
					(	int const	control,
						void *		data
					);

	/** . @copydoc IParserRecorder::Record */
	virtual void	Record
					(	irid const	irid,
						int const	x,
						int const	y,
						int const	size
					);

};

}

#endif
