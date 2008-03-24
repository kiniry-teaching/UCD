phoney:
	# usage:
	#  make ceb  - compile cygwin compatible eb version
	#  make cet  - compile cygwin compatible eb test version
	#  make leb  - compile linux compatible eb version (haven't tested this yet)
	#  todo: support for Mac OS X

ceb:
	g++ eb_main.cpp rai/*/*.cpp -D __EB__ -lglut32 -lopengl32 -o kinephon.exe

cet:
	g++ eb_main.cpp rai/*/*.cpp -D __EB__ -D __TEST__ -lglut32 -lopengl32 -o kinephon.exe

leb:
	g++ eb_main.cpp rai/*/*.cpp -D __EB__ -lglut -lGL -o kinephon.exe
