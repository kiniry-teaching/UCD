#ifndef __INTERPRETER_TRACK_H__
#define __INTERPRETER_TRACK_H__

#include "Frame.h"

/*
 * Author:	EB
 *
 * Store all the frames for a single IR blob
 *
 */
namespace interpreter
{

class Track
{

				// Be friends with Recorder so it can add frames
	friend		class Recorder;

public:
	/**/		Track
				(	int const	id
				);
	virtual		~Track			(void);
				// Get the id of the blob that this track records
	int			id				(void)	const;
				// Get the number of frames
	int			length			(void)	const;
				// Get the first frame in the list of frames
	Frame *		frames			(void)	const;

				// Return a frame by index
	Frame *		operator []
				(	int const	index
				)	const;

private:
				// Add the next frame to the end of the list
	void		next
				(	Frame const * const	next
				);

private:
				// Store the id of the blob that this track records
	int			_id;
				// First in linked list of frames in track
	Frame *		_frameFirst;
				// Last in linked list of frames in track, for quick add
	Frame *		_frameLast;

};

}

#endif
