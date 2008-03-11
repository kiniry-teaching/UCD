phony:
	# usage:
	#  make ceb  - compile cygwin compatible eb version
	#  make leb  - compile linux compatible eb version (haven't tested this yet)
	#  todo: support for Mac OS X

ceb:
	g++ *.cpp rai/*/*.cpp -D __EB__ -lglut32 -lopengl32 -o kinephon.exe

leb:
	g++ *.cpp rai/*/*.cpp -D __EB__ -lglut -lGL -o kinephon.exe
