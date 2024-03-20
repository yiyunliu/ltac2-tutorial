COQDOCJS_DIR ?= coqdocjs
EXTRA_DIR = $(COQDOCJS_DIR)/extra
COQDOCFLAGS ?= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQDOCJS_LN?=false
-include coqdocjs/Makefile.doc
COQMAKEFILE?=Makefile.coq

all: theories

theories: $(COQMAKEFILE)
	$(MAKE) -f $^

$(COQMAKEFILE):
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

coqdoc: $(COQMAKEFILE)
	$(MAKE) -f $^ html
ifeq ($(COQDOCJS_LN),true)
	ln -sf ../$(EXTRA_DIR)/resources html
else
	cp -R $(EXTRA_DIR)/resources html
endif

install: $(COQMAKEFILE)
	$(MAKE) -f $^ install

clean:
	if [ -e $(COQMAKEFILE) ] ; then $(MAKE) -f $(COQMAKEFILE) cleanall ; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

uninstall:
	$(MAKE) -f $(COQMAKEFILE) uninstall

dist:
	@ git archive --prefix ltac2-tutorial/ HEAD -o $(PROJECT_NAME).tgz

.PHONY: all clean dist theories coqdoc

TEMPLATES ?= ../templates
