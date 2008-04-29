@if exist C:\software.key\sync.exe C:\software.key\sync
java -classpath .;Phidget21.jar -ea selfCheckOut.ScalesServer
@if exist C:\software.key\sync.exe C:\software.key\sync
