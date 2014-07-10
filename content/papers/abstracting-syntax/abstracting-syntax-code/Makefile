############################################################################
#
#  Primary targets:
#    all           - builds .vo files and coqwc
#    coq           - synonym for 'all'
#    clean         - removes all generated files
#    documentation - builds HTML documentation
#
############################################################################

DOCDIR = doc

## Paths to executables. Do not include options here.

COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc

## List of files to be compiled *and* documented.

FILES = \
	AdditionalTactics \
	Atom \
	Environment \
	FiniteSets \
	FSetDecide \
	FSetNotin \
	ListFacts \
	Metatheory \
	\
	Common \
	\
	Fsub_LetSum_Definitions \
	Fsub_LetSum_Infrastructure \
	Fsub_LetSum_Soundness \
	\
	Collapsed_Definitions \
	Collapsed_Infrastructure \
	Collapsed_Soundness \
	Collapsed_Adequacy \
	\
	Tagged_Definitions \
	Tagged_Infrastructure \
	Tagged_Soundness \
	Tagged_Adequacy \
	\
	HOAS_Object_Definitions \
	HOAS_Object_Infrastructure \
	HOAS_Object_Soundness \
	HOAS_Object_Adequacy \
	\
	Lib_Untyped_Lambda \
	HOAS_Untyped_Definitions \
	HOAS_Untyped_Soundness \
	HOAS_Untyped_Adequacy \
	\
	Lib_Typed_Lambda \
	HOAS_Typed_Definitions \
	HOAS_Typed_Soundness \
	HOAS_Typed_Adequacy \

## List of all files that need to be compiled.

ALLFILES = $(FILES)

## Lists calculated from the above.

VFILES  = $(foreach i, $(FILES), $(i).v)
VOFILES = $(foreach i, $(FILES), $(i).vo)
GLOBS   = $(foreach i, $(FILES), -glob-from $(i).glob)

ALLVFILES    = $(foreach i, $(ALLFILES), $(i).v)
ALLVOFILES   = $(foreach i, $(ALLFILES), $(i).vo)
ALLGLOBFILES = $(foreach i, $(ALLFILES), $(i).glob)


############################################################################

.PHONY: all clean coq documentation counts
.SECONDARY: $(ALLGLOBFILES)
.SUFFIXES: .v .vo

all : coq

coq : $(ALLVOFILES) coqwc

documentation : $(VFILES) $(DOCDIR)
	$(COQDOC) -g --quiet --utf8 --html -d $(DOCDIR) $(VFILES)
	cp -f custom.css $(DOCDIR)/coqdoc.css

counts : coqwc
	./coqwc Fsub_LetSum*.v
	./coqwc Collapsed*.v
	./coqwc Tagged*.v
	./coqwc HOAS_Object*.v
	./coqwc HOAS_Untyped*.v

clean :
	rm -f *.vo *.glob *.cmi *.cmx *.o
	rm -rf $(DOCDIR) coqwc coqwc.ml


############################################################################

$(DOCDIR) :
	mkdir -p $(DOCDIR)

coqwc : coqwc.mll
	ocamllex coqwc.mll
	ocamlopt -o coqwc coqwc.ml

%.vo : %.v
	$(COQC) -q -I . $<


############################################################################

.depend : $(ALLVFILES)
	$(COQDEP) -I . $(ALLVFILES) > .depend

include .depend
