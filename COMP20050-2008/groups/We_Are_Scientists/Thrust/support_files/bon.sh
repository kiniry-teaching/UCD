#!/bin/sh
echo -n "class_chart "
# iterate through words until we see class and take next word and toupper it
cat $1 | awk '/class/ { print toupper($4) }' -

echo "explanation"
echo -n "  \""
echo -n `cat $1 | grep '@explanation' | sed s/\*// | sed s/@explanation//`
echo "\""

echo "indexing"
# split the input line on ':' and take what is before the colon
end_of_header_line_number=`grep -n class $1 | awk -F: '{ print $1 }'`
# echo $end_of_header_line_number
cat $1 | head -$end_of_header_line_number | grep '@' | sed s/\*// | sed s/@//

echo "query"
# find all the queries and strip out the * at the beginning
cat $1 | grep "\?" | sed s/\*// | sed s/@return//

echo "command"
# find all the commands and strip out the * at the beginning
cat $1 | grep '\* '[A-Z] $i | sed s/\*//

echo "constraint"
# find all the contraints and strip out the * at the beginning and the @constraint
cat $1 | grep @constraint | sed s/\*// | sed s/@constraint//

echo "end"


