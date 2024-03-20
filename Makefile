all: theories

COQDOCJS_LN?=true
-include coqdocjs/Makefile.doc
COQMAKEFILE?=Makefile.coq

theories: $(COQMAKEFILE)
	$(MAKE) -f $^

$(COQMAKEFILE):
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

html: $(COQMAKEFILE)
	$(MAKE) -f $^ html

install: $(COQMAKEFILE)
	$(MAKE) -f $^ install

clean:
	if [ -e $(COQMAKEFILE) ] ; then $(MAKE) -f $(COQMAKEFILE) cleanall ; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

uninstall:
	$(MAKE) -f $(COQMAKEFILE) uninstall

dist:
	@ git archive --prefix ltac2-tutorial/ HEAD -o $(PROJECT_NAME).tgz

.PHONY: all clean dist theories html

TEMPLATES ?= ../templates
