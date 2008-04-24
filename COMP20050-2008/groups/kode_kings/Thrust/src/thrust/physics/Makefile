#
# Thrust Makefile
# Makefile
# COMP 20050
# by Joe Kiniry
# version 1 April 2008
#

TEAMNAME = TeamAmerica
PROJECT_ROOTDIR = `pwd`

java_source = $(wildcard thrust/**/*.java)

JMLC = jmlc
JMLDOC = jmldoc
ESCJAVA2 = escjava2
CHECKSTYLECP = /usr/local/java/checkstyle/checkstyle-optional.jar:/usr/local/java/checkstyle/checkstyle-all.jar
REL_ROOT = ..

.PHONY: all build docs
.PHONY: javac typecheck_specs jmlc esc bon
.PHONY: javadoc jmldoc
.PHONY: checkstyle
.PHONY: archive
.PHONY: clean realclean

all:	javac typecheck_specs jmlc esc docs # checkstyle

build:	javac jmlc

docs:	javadoc # jmldoc

javac:	.javac

.javac:	$(java_source)
	mkdir -p $(REL_ROOT)/classes;
	javac -d $(REL_ROOT)/classes $(java_source) && touch .javac

typecheck_specs:	.typecheck

.typecheck:	$(java_source)
	$(ESCJAVA2) -source 1.4 -typecheck $(java_source) && touch .typecheck

jmlc:	.jmlc

.jmlc:	$(java_source)
	mkdir -p $(REL_ROOT)/jmlrac_classes;
	$(JMLC) --Quiet --source 1.4 -d $(REL_ROOT)/jmlrac_classes $(java_source) && touch .jmlc

esc:  .esc

.esc:  $(java_source)
	$(ESCJAVA2) -source 1.4 $(java_source) && touch .esc

jmldoc:  .jmldoc

.jmldoc:  $(java_source)
	mkdir -p $(REL_ROOT)/jmldoc;
	$(JMLDOC) -source 1.4 -protected -d $(REL_ROOT)/jmldoc $(java_source) && touch .jmldoc

javadoc:  .javadoc

.javadoc:  $(java_source)
	mkdir -p $(REL_ROOT)/javadoc;
	javadoc -source 1.4 -protected -d $(REL_ROOT)/javadoc $(java_source) && touch .javadoc

.bon:  
	mkdir -p $(REL_ROOT)/bon;
	for i in $(java_source); \
	  do $(REL_ROOT)/bon.sh $$i > $(REL_ROOT)/bon/`basename $$i .java`.bon; \
	done && touch .bon;

bon:  .bon

.checkstyle:	$(java_source)
	export CLASSPATH=$(CHECKSTYLECP):$(CLASSPATH); \
	java com.puppycrawl.tools.checkstyle.Main \
	  -c $(REL_ROOT)/csi.xml $(java_source) && touch .checkstyle

checkstyle:	.checkstyle

archive:
	(cd $(REL_ROOT)/..; rm -f $(TEAMNAME).tgz;)
	(cd $(REL_ROOT); tar czf ../$(TEAMNAME).tgz .)

clean:
	rm -rf .typecheck .javac .jmlc .jmldoc .javadoc .bon .checkstyle .esc
	rm -rf $(REL_ROOT)/classes $(REL_ROOT)/jmlrac_classes $(REL_ROOT)/jmldoc $(REL_ROOT)/javadoc $(REL_ROOT)/bon

realclean:	clean
	find $(REL_ROOT) -name "*~" -or -name ".#*" -exec rm -f {} \;
	find $(REL_ROOT) -name "semantic.cache" -exec rm -f {} \;
	(cd $(REL_ROOT)/..; rm -f $(TEAMNAME).tgz;)
