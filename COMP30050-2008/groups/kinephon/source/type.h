#ifndef __TYPE_H__
#define __TYPE_H__

/**
 * unsigned char shorthand
 * @author EB
 * @version 1.0
 */
typedef unsigned char	uchar;
/**
 * unsigned short shorthand
 * @author EB
 * @version 1.0
 */
typedef unsigned short	ushort;
/**
 * unsigned int shorthand
 * @author EB
 * @version 1.0
 */
typedef unsigned int	uint;
/**
 * unsigned long shorthand
 * @author EB
 * @version 1.0
 */
typedef unsigned long	ulong;

/**
 * IR Blob identifier
 * @author EB
 * @version 1.0
 */
typedef uint			irid;
/**
 * Count number of milliseconds from program start
 * @author EB
 * @version 1.0
 */
typedef uint			tick;
/**
 * Shape identifier
 * @author EB
 * @version 1.0
 */
typedef uint			sid;
/**
 * Enumerated control type
 * @author EB
 * @version 1.0
 * @see econtrol
 */
typedef uchar			ect;
/**
 * Enumerated shape type
 * @author EB
 * @version 1.0
 * @see etype
 */
typedef uchar			est;
/**
 * Enumerated zone compare mode
 * @author EB
 * @version 1.0
 * @see ezmode
 */
typedef uchar			ezm;
/**
 * Enumerated zone result
 * @author EB
 * @version 1.0
 * @see ezresult
 */
typedef uchar			ezr;
/**
 * Enumerated sharp side prune
 * @author EB
 * @version 1.0
 * @see eprune
 */
typedef bool			esp;
/**
 * Enumerated point raw access
 * @author EB
 * @version 1.0
 * @see epoint
 */
typedef int				epr;

/**
 * Pure virtual function modifier
 * @author EB
 * @version 1.0
 */
#define					pure = 0

#endif
