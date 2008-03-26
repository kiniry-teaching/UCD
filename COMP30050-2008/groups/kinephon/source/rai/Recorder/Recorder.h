#ifndef __INTERPRETER_RECORDER_H__
#define __INTERPRETER_RECORDER_H__

#include <vector>
#include "../../type.h"
#include "IParserRecorder.h"
#include "Track.h"
#include "Recording.h"
using std::vector;

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

#if __TEST__
///////////////////////////////////////////////////////////////////////////////
// tests
//
public:
	/**
	 * Execute a number of test cases for this class
	 * @author EB
	 * @version 1.0
	 */
	static void	RunTest			(void);
#endif

///////////////////////////////////////////////////////////////////////////////
// commands
//
public:
	/**
	 * Eject the recording from the Recorder.
	 * Takes a copy of the recorded track up to this point. The Recorder
	 *	will still contain this copied data, so calling Eject again will
	 *	return the same track data, possibly with new frames add at the
	 *	end. To remove consumed frames from a track, call Erase.
	 * @return A copy of the recording at this point in time
	 * @author EB
	 * @version 1.0
	 */
	Recording *			eject			(void)		const;
	/**
	 * Erase frames from a track.
	 * All frames before and including the specified frame are removed from
	 *	the track that is recording the speicified IR blob
	 * @param iid IR blob whose track is to be erased
	 * @param frameIndex All frames from this and before are removed from the
	 *	track. If frameIndex is -1 (default), the whole track is erased
	 * @author EB
	 * @version 1.0
	 */
	void				erase
						(	irid const	iid,
							uint const	frameIndex	= ~0
						);
	/**
	 * Erase a Recording previously obtained through eject()
	 * @param recording The recording returned from eject. This pointer
	 *	should not be used after calling this function
	 * @author EB
	 * @version 1.0
	 */
	void				erase
						(	Recording *	recording
						);

///////////////////////////////////////////////////////////////////////////////
// interface
//
public:
	/**
	 * Issue a control switch.
	 * Used to add or remove IR blob ids, indicate errors
	 * @param control Control switch to make.
	 * @param iid If IR id for which the control action has occurred
	 * @return If the control needs to respond, it will be returned here. Each
	 *	control will specify what is returned. Values are enumerated in
	 *	econtrol
	 * @see econtrol
	 */
	virtual int			control
						(	ect const	control,
							irid const	iid
						);
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
	virtual void		record
						(	irid const	iid,
							int const	x,
							int const	y,
							int const	size,
							tick const	time
						);

///////////////////////////////////////////////////////////////////////////////
// private commands
//
private:
	/**
	 * Get a track by it's IR id
	 * This is a const function, but I couldn't specify that it's const
	 *	as the vector iterator complains
	 * @param iid The id of the track to get
	 * @return A pointer to the requested track or 0 if not found
	 * @author EB
	 * @version 1.0
	 */
	Track *				findTrack
						(	irid const	iid
						);
	/**
	 * Find and remove a track from the recorder
	 * @param iid The id of the track to erase
	 * @author EB
	 * @version 1.0
	 */
	void				eraseTrack
						(	irid const	iid
						);
	/**
	 * control() econtrol::FOUND Helper
	 * @param iid IR blob whose track is to be erased
	 * @return always 0
	 * @author EB
	 * @version 1.0
	 */
	int					controlFound
						(	irid const	iid
						);
	/**
	 * control() econtrol::LOST Helper
	 * @param iid IR blob whose track is to be erased
	 * @return always 0
	 * @author EB
	 * @version 1.0
	 */
	int					controlLost
						(	irid const	iid
						);
	/**
	 * control() econtrol::BADCOM Helper
	 * @return always 0
	 * @author EB
	 * @version 1.0
	 */
	int					controlBadcom	(void);

///////////////////////////////////////////////////////////////////////////////
// fields
//
private:
	/**
	 * Contains an array of the Recorder's tracks. This array may be re-allocated
	 *	as IR blob are control::LOST and control::FOUND
	 * @author EB
	 * @version 1.0
	 */
	vector<Track*>		_tracks;

};

}

#endif
