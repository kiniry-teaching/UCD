#ifndef __INTERPRETER_PATTERN_H__
#define __INTERPRETER_PATTERN_H__

/*
 * Author:	EB
 *
 * Base class for building instrument patterns
 *
 */
namespace Interpreter
{

class Pattern
{

public:
	/**/				Pattern		(void);
	virtual				~Pattern	(void);

public:
	Bar const * const	Compose		(void);

};

}

#endif
