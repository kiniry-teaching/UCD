#ifndef EXAMPLE_H_
#define EXAMPLE_H_

/// Brief description of class here
/**
 * Detailed description of class here
 */
class Example
{
public:
	Example();
	virtual ~Example();

	/// Insert brief description of function
	/**
	 * Insert detailed description of function. Can HTML or <code>...</code> tag
	 *  as well as features described in doxygen help
	 * Also fill the details of the following tags, note. the param and return
	 *  are 'required' even if purpose is obvious.
	 * @param       exParam1 Insert brief of exParam1
	 * @param       exParam2 Insert brief of exParam2
	 * @return      Insert brief of return value (methods only)
	 * @exception   Insert brief of exceptions thrown
	 * @author      Insert initials
	 * @version     Will we use this?
	 * @see         How is this used?
	 * @since       What's the purpose of this?
	 */
	int sampleMethod(int exParam1, int exParam2);
};

#endif /*EXAMPLE_H_*/
