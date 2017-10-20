############################################################################
# You can define your own path to COQBIN and to TLC by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#
# TLC=~/tlc/trunk
# COQBIN=/var/tmp/coq-8.3pl2/bin/
#
# Note that TLC should have no leading slash, whereas COQBIN should have one.
# Note that if you rebind COQBIN you need to do the same in the TLC folder.
# Note that if you add a settings.sh file, you will need to do "make depend".

# Default paths are as follows:

TLC=../tlc
COQBIN=

############################################################################

INCLUDES=-R $(TLC) TLC

COQC=$(COQBIN)coqc $(INCLUDES)
COQDEP=$(COQBIN)coqdep $(INCLUDES)
COQDOC=$(COQBIN)coqdoc --quiet --utf8 --html

############################################################################

FILES=\
	DeclDef\
	DeclInfra\
	DeclProp\
	PBCDef\
	PBCInfra\
	PBCProp\
	Translation\
	DeclSub\
	DeclTyping\
	DeclSub\
	Criteria\

ALL=$(FILES)

############################################################################

ALL_SRC=$(ALL:=.v)
TLC_SRC=$(wildcard $(TLC)/*.v)
DEP_SRC=$(ALL_SRC) $(TLC_SRC)

.PHONY: all tlc clean clean-tlc distclean
.SUFFIXES: .v .vo

all: $(ALL:=.vo)

tlc:
	make -C $(TLC) lib

.v.vo : .depend
	$(COQC) $<

weak: $(WEAKCAST:=.vo)
full: $(FULLCAST:=.vo)
cocmu: $(COCMU:=.vo)

#######################################################

depend: .depend

.depend : $(DEP_SRC) Makefile
	$(COQDEP) $(DEP_SRC) > .depend

ifeq ($(findstring $(MAKECMDGOALS),depend clean clean-tlc distclean),)
include .depend
endif

clean :
	rm -f *.vo .depend *.deps *.dot *.glob .*.aux

clean-tlc :
	@rm -f $(TLC)/*.vo $(TLC)/*.glob $(TLC)/*.v.d $(TLC)/.*.aux || echo ok

distclean : clean clean-tlc

############################################################################
#
#coqdoc :
#	@mkdir -p doc_light
#	$(COQDOC) --gallina -d doc_light $(VFILES)
#
