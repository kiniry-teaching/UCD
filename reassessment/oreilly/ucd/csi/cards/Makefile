#
# Cards Makefile
# Makefile
# COMP 20050
# by Joe Kiniry
# version 29 November 2008
#

java_source = $(wildcard source/ucd/csi/cards/*.java)

JAVAC = javac
JAVADOC = usr/bin/javadoc -source 1.4
JMLC = /opt/bin/jmlc -source 1.4
JMLDOC = /opt/bin/jmldoc -source 1.4
ESCJAVA2 = /opt/bin/escjava2 -source 1.4
CHECKSTYLECP = /opt/java/checkstyle/checkstyle-optional.jar:/opt/java/checkstyle/checkstyle-all.jar

.PHONY: all build docs
.PHONY: javac typecheck_specs jmlc esc bon
.PHONY: javadoc jmldoc
.PHONY: checkstyle
.PHONY: archive
.PHONY: clean realclean

all:	javac typecheck_specs jmlc esc docs bon checkstyle

build:	javac jmlc

docs:	javadoc jmldoc

javac:	.javac

.javac:	$(java_source)
	mkdir -p classes;
	$(JAVAC) -sourcepath source -d classes $(java_source) && touch .javac

typecheck_specs:	.typecheck

.typecheck:	$(java_source)
	$(ESCJAVA2) -sourcepath source -typecheck $(java_source) && touch .typecheck

jmlc:	.jmlc

.jmlc:	$(java_source)
	mkdir -p jmlrac_classes;
	$(JMLC) --sourcepath source:/usr/local/Java/JML/specs --Quiet -d jmlrac_classes $(java_source) && touch .jmlc
# --Quiet, --verbose, --debug

esc:  .esc

.esc:  $(java_source)
	$(ESCJAVA2) -sourcepath source $(java_source) && touch .esc

jmldoc:  .jmldoc

.jmldoc:  $(java_source)
	mkdir -p jmldoc;
	$(JMLDOC) --sourcepath source -protected -d jmldoc $(java_source) && touch .jmldoc

javadoc:  .javadoc

.javadoc:  $(java_source)
	mkdir -p javadoc;
	$(JAVADOC) -protected -quiet -d javadoc $(java_source) && touch .javadoc

.bon:  
	mkdir -p bon;
	for i in $(java_source); \
	  do ./bon.sh $$i > bon/`basename $$i .java`.bon; \
	done && touch .bon;

bon:  .bon

.checkstyle:	$(java_source)
	export CLASSPATH=$(CHECKSTYLECP):$(CLASSPATH); \
	java com.puppycrawl.tools.checkstyle.Main \
	  -c csi.xml $(java_source) && touch .checkstyle

checkstyle:	.checkstyle

archive:
	(cd ..; rm -f cards.tgz;)
	(cd ..; tar czf cards.tgz \
	  COMP20050/Makefile COMP20050/csi.xml COMP20050/bon.sh \
	  COMP20050/CA.txt COMP20050/Template.java \
	  ucd/csi/cards/Card.java \
	  ucd/csi/cards/PokerCard.java \
	  ucd/csi/cards/PokerHand.java \
	  ucd/csi/cards/PokerDeck.java \
	  ucd/csi/cards/Main.java 	  

clean:
	rm -rf .typecheck .javac .jmlc .jmldoc .javadoc .bon .checkstyle .esc
	rm -rf classes/* jmlrac_classes doc jmldoc javadoc bon

realclean:	clean
	find . -name "*~" -or -name ".#*" -or -name "*.class" -exec rm -f {} \;
	find . -name "semantic.cache" -exec rm -f {} \;
	(cd ..; rm -f cards.tgz;)
