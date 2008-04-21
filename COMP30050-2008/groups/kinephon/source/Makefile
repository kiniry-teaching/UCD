WARN =	-Wextra -Wunused -Wcast-align -Wdeprecated-declarations -Wdisabled-optimization \
		-Wmissing-noreturn -Wpacked -Wstrict-aliasing -Wswitch -Wswitch-enum \
		-Wuninitialized -Wctor-dtor-privacy -Wdeprecated -Wnon-virtual-dtor \
		-Wold-style-cast -Woverloaded-virtual -Wpmf-conversions -Wreorder -Wsign-promo -O

phoney:
	# usage:
	#  make win  - compile for cygwin
	#  make lin  - compile for linux
	#
	#  make ceb  - compile cygwin compatible eb version
	#  make cet  - compile cygwin compatible eb test version
	#  make leb  - compile linux compatible eb version (haven't tested this yet)
	#  todo: support for Mac OS X

win:
	g++ audio/*.cpp rai/*/*.cpp config.cpp main.cpp -D __KP__ ${WARN} -lglut32 -lopengl32 -o kinephon.exe

lin:
	g++ audio/*.cpp rai/*/*.cpp config.cpp main.cpp -D __KP__ ${WARN} -lglut -lGL -o -o kinephon.exe


ceb:
	g++ rai/*/*.cpp eb_main.cpp -D __EB__ ${WARN} -lglut32 -lopengl32 -o kinephon.exe

cet:
	g++ rai/*/*.cpp eb_main.cpp -D __EB__ ${WARN} -D __TEST__ -lglut32 -lopengl32 -o kinephon.exe

leb:
	g++ rai/*/*.cpp eb_main.cpp -D __EB__ ${WARN} -lglut -lGL -o kinephon.exe
