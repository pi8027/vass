include ./.deps

COQLIBS=-R coq Vass ${COQLIBS}
VOFILES=$(VFILES:.v=.vo)
GLOBFILES=$(VFILES:.v=.glob)

.DEFAULT_GOAL := all
.PHONY: all clean

all: ${VOFILES}

clean:
	rm -f .deps ${VOFILES} ${GLOBFILES}

.deps: ${VFILES}
	coqdep -c -w -slash ${COQLIBS} ${VFILES} > .deps

%.vo %.glob: %.v
	coqc -q ${COQLIBS} $*
