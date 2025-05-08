# Makefile for Coq project

# Compiler and compiler flags
COQC = coqc
# COQFLAGS = -R . NeuroCert

# List of Coq source files
COQ_FILES = Facts.v Neuron.v SortList.v Circuit.v Archetype.v Test.v Composition.v Equiv.v PropCompo.v


# Targets
all: $(COQ_FILES:.v=.vo)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

clean:
	rm -f *.vo *.glob

.PHONY: all clean
