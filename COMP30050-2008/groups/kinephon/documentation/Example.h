#ifndef EXAMPLE_H_
#define EXAMPLE_H_

class Example
{
public:
	Example();
	virtual ~Example();
	//taken from 
	//http://java.sun.com/j2se/javadoc/writingdoccomments/
	/**
	 * This first sentence will appear in the class interface summary.
	 * The rest of the text will appear in the detailed description.
	 * Use <code>...</code> for highlighting keywords and (class/method etc.)names.
	 * <p>
	 * Include the following tags (where necessary) in THIS order. 
	 * The param and return are 'required' even if purpose is obvious.
	 * @param       (classes, interfaces, methods and constructors only)
	 * @return      (methods only)
	 * @exception   (@throws is a synonym added in Javadoc 1.2)
	 * @author      (classes and interfaces only, required)
	 * @version     (classes and interfaces only, required. See footnote 1)
	 * @see         
	 * @since       
	 * @serial      (or @serialField or @serialData)
	 * @deprecated  (see How and When To Deprecate APIs)
	 */
	int sampleMethod(int exParam);
};

#endif /*EXAMPLE_H_*/
