# Microsoft Developer Studio Project File - Name="kinephon" - Package Owner=<4>
# Microsoft Developer Studio Generated Build File, Format Version 6.00
# ** DO NOT EDIT **

# TARGTYPE "Win32 (x86) Application" 0x0101

CFG=kinephon - Win32 Test
!MESSAGE This is not a valid makefile. To build this project using NMAKE,
!MESSAGE use the Export Makefile command and run
!MESSAGE 
!MESSAGE NMAKE /f "kinephon.mak".
!MESSAGE 
!MESSAGE You can specify a configuration when running NMAKE
!MESSAGE by defining the macro CFG on the command line. For example:
!MESSAGE 
!MESSAGE NMAKE /f "kinephon.mak" CFG="kinephon - Win32 Test"
!MESSAGE 
!MESSAGE Possible choices for configuration are:
!MESSAGE 
!MESSAGE "kinephon - Win32 Release" (based on "Win32 (x86) Application")
!MESSAGE "kinephon - Win32 Debug" (based on "Win32 (x86) Application")
!MESSAGE "kinephon - Win32 Test" (based on "Win32 (x86) Application")
!MESSAGE 

# Begin Project
# PROP AllowPerConfigDependencies 0
# PROP Scc_ProjName ""
# PROP Scc_LocalPath ""
CPP=cl.exe
MTL=midl.exe
RSC=rc.exe

!IF  "$(CFG)" == "kinephon - Win32 Release"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 0
# PROP BASE Output_Dir "Release"
# PROP BASE Intermediate_Dir "Release"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 0
# PROP Output_Dir "Release"
# PROP Intermediate_Dir "Release"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /GX /O2 /D "WIN32" /D "NDEBUG" /D "_WINDOWS" /D "_MBCS" /YX /FD /c
# ADD CPP /nologo /W3 /GX /O2 /D "WIN32" /D "NDEBUG" /D "_CONSOLE" /D "_MBCS" /D "__WINDOWS_MM__" /D "__EB__" /YX /FD /c
# ADD BASE MTL /nologo /D "NDEBUG" /mktyplib203 /win32
# ADD MTL /nologo /D "NDEBUG" /mktyplib203 /win32
# ADD BASE RSC /l 0x1809 /d "NDEBUG"
# ADD RSC /l 0x1809 /d "NDEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LINK32=link.exe
# ADD BASE LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /subsystem:windows /machine:I386
# ADD LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /subsystem:console /profile /machine:I386

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 1
# PROP BASE Output_Dir "Debug"
# PROP BASE Intermediate_Dir "Debug"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 1
# PROP Output_Dir "Debug"
# PROP Intermediate_Dir "Debug"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /Gm /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_WINDOWS" /D "_MBCS" /YX /FD /GZ /c
# ADD CPP /nologo /W3 /Gm /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_CONSOLE" /D "_MBCS" /D "__WINDOWS_MM__" /D "__EB__" /D "__MEMORY__" /FR /YX /FD /GZ /c
# ADD BASE MTL /nologo /D "_DEBUG" /mktyplib203 /win32
# ADD MTL /nologo /D "_DEBUG" /mktyplib203 /win32
# ADD BASE RSC /l 0x1809 /d "_DEBUG"
# ADD RSC /l 0x1809 /d "_DEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LINK32=link.exe
# ADD BASE LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /subsystem:windows /debug /machine:I386 /pdbtype:sept
# ADD LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib winmm.lib /nologo /subsystem:console /debug /machine:I386
# SUBTRACT LINK32 /profile
# Begin Special Build Tool
SOURCE="$(InputPath)"
PostBuild_Cmds="C:\Data\College\COMP30050 - Software Engerineering Project III\kinephon\source\dox"
# End Special Build Tool

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 1
# PROP BASE Output_Dir "kinephon___Win32_Test"
# PROP BASE Intermediate_Dir "kinephon___Win32_Test"
# PROP BASE Ignore_Export_Lib 0
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 1
# PROP Output_Dir "kinephon___Win32_Test"
# PROP Intermediate_Dir "kinephon___Win32_Test"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /Gm /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_CONSOLE" /D "_MBCS" /D "__WINDOWS_MM__" /D "__EB__" /FR /YX /FD /GZ /c
# ADD CPP /nologo /W3 /Gm /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_CONSOLE" /D "_MBCS" /D "__WINDOWS_MM__" /D "__EB__" /D "__TEST__" /FR /YX /FD /GZ /c
# ADD BASE MTL /nologo /D "_DEBUG" /mktyplib203 /win32
# ADD MTL /nologo /D "_DEBUG" /mktyplib203 /win32
# ADD BASE RSC /l 0x1809 /d "_DEBUG"
# ADD RSC /l 0x1809 /d "_DEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LINK32=link.exe
# ADD BASE LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib winmm.lib /nologo /subsystem:console /debug /machine:I386 /pdbtype:sept
# SUBTRACT BASE LINK32 /pdb:none
# ADD LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib winmm.lib /nologo /subsystem:console /debug /machine:I386 /pdbtype:sept
# SUBTRACT LINK32 /pdb:none
# Begin Special Build Tool
SOURCE="$(InputPath)"
PostBuild_Cmds="C:\Data\College\COMP30050 - Software Engerineering Project III\kinephon\source\dox"
# End Special Build Tool

!ENDIF 

# Begin Target

# Name "kinephon - Win32 Release"
# Name "kinephon - Win32 Debug"
# Name "kinephon - Win32 Test"
# Begin Group "audio"

# PROP Default_Filter ""
# Begin Source File

SOURCE=.\audio\Channel.cpp

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\Channel.h

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\Conductor.cpp

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\Conductor.h

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\MidiPlayer.cpp

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\MidiPlayer.h

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\MidiRecorder.cpp

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\MidiRecorder.h

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\midiTest.cpp

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\RtError.h

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\RtMidi.cpp

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\audio\RtMidi.h

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

!ENDIF 

# End Source File
# End Group
# Begin Group "rai"

# PROP Default_Filter ""
# Begin Group "interpreter"

# PROP Default_Filter ""
# End Group
# Begin Group "recorder"

# PROP Default_Filter ""
# Begin Source File

SOURCE=.\rai\Recorder\Frame.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Recorder\Frame.h
# End Source File
# Begin Source File

SOURCE=.\rai\Recorder\IParserRecorder.h
# End Source File
# Begin Source File

SOURCE=.\rai\Recorder\Recorder.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Recorder\Recorder.h
# End Source File
# Begin Source File

SOURCE=.\rai\Recorder\Recording.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Recorder\Recording.h
# End Source File
# Begin Source File

SOURCE=.\rai\Recorder\Track.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Recorder\Track.h
# End Source File
# End Group
# Begin Group "analyser"

# PROP Default_Filter ""
# Begin Source File

SOURCE=.\rai\Analyser\Math.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\Math.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\Point.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\Points.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\Points.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\Shape.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\Shape.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapeAccel.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapeAccel.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapeMatch.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapeMatches.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapeMatches.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapeMovement.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapeMovement.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\Shapes.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\Shapes.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapesLoader.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapesLoader.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapeSpeed.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\ShapeSpeed.h
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\Zone.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\Zone.h
# End Source File
# End Group
# Begin Group "tests"

# PROP Default_Filter ""
# Begin Source File

SOURCE=.\rai\Recorder\TestFrame.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\TestImage.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\TestImage.h
# End Source File
# Begin Source File

SOURCE=.\rai\TestMemory.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\TestMemory.h
# End Source File
# Begin Source File

SOURCE=.\rai\Recorder\TestRecorder.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\TestShapeMatches.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\TestShapesLoader.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Recorder\TestTrack.cpp
# End Source File
# Begin Source File

SOURCE=.\rai\Analyser\TestZone.cpp
# End Source File
# End Group
# Begin Source File

SOURCE=.\rai\ShapeId.h
# End Source File
# End Group
# Begin Source File

SOURCE=.\config.cpp
# End Source File
# Begin Source File

SOURCE=.\config.h
# End Source File
# Begin Source File

SOURCE=.\eb_main.cpp
# End Source File
# Begin Source File

SOURCE=.\main.cpp
# End Source File
# Begin Source File

SOURCE=.\Makefile

!IF  "$(CFG)" == "kinephon - Win32 Release"

!ELSEIF  "$(CFG)" == "kinephon - Win32 Debug"

# PROP Exclude_From_Build 1

!ELSEIF  "$(CFG)" == "kinephon - Win32 Test"

# PROP BASE Exclude_From_Build 1
# PROP Exclude_From_Build 1

!ENDIF 

# End Source File
# Begin Source File

SOURCE=.\type.h
# End Source File
# End Target
# End Project
