# Maintained build entry point for the Coq development.
#
# Every invocation first regenerates Makefile.coq from _CoqProject with
# coq_makefile and then delegates the requested goals to it, so edits to
# _CoqProject take effect without a manual regeneration step.  Makefile.coq,
# Makefile.coq.conf, and the .*.d dependency files are generated artifacts
# (see .gitignore); this wrapper is the committed interface.
#
#   make                     build everything (default; no assumption reports)
#   make check               opt-in audit: build the project, print assumptions,
#                             and compile the paper-claims index
#   make clean               delegate clean and also remove the audit's outputs
#   make layers              check that imports respect scripts/layers.txt
#                             (python3; runs as its own CI step)
#   make GOAL...             any other goal passes through to Makefile.coq
#                             (file targets like Lib/Arrow/Arrow.vo, install, ...)
#
# Parallel builds (make -jN) and multiple build goals use a single sub-make
# through the jobserver. If clean is also requested, it completes before the
# shared build; assumption reporting runs afterward.

COQ_MAKEFILE ?= coq_makefile
COQPROJECT   := _CoqProject
COQMAKEFILE  := Makefile.coq
COQC         ?= coqc
COQDEBUG     ?=
COQFLAGS     ?= -q
# Single source of truth for load-path flags: the -Q/-R lines of _CoqProject.
COQLIBS      := $(shell grep -E '^-[QR][[:space:]]' $(COQPROJECT))

.DEFAULT_GOAL := all

.PHONY: regen
regen:
	$(COQ_MAKEFILE) -f $(COQPROJECT) -o $(COQMAKEFILE)

.PHONY: all
all: delegate

# The audit is deliberately outside _CoqProject, so the normal build never
# compiles it and the generated clean rule never removes its outputs.  Its
# dependency closure lies inside the normal build, so building everything
# first suffices; no prerequisite list is maintained here.
.PHONY: check
check: delegate
	$(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) Checks/Assumptions.v
	@# The claims index only has to compile: every name in PAPER.md exists.
	$(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) Checks/PaperClaims.v > /dev/null
	@echo "Checks/PaperClaims.v: all paper claims resolve"

.PHONY: layers
layers:
	python3 scripts/depgraph.py --check-layers

.PHONY: clean
clean: regen
	$(MAKE) -f $(COQMAKEFILE) clean
	rm -f Checks/Assumptions.vo Checks/Assumptions.vos Checks/Assumptions.vok \
	  Checks/Assumptions.glob Checks/.Assumptions.aux \
	  Checks/PaperClaims.vo Checks/PaperClaims.vos Checks/PaperClaims.vok \
	  Checks/PaperClaims.glob Checks/.PaperClaims.aux

# Share one dependency graph across all/check and explicit file/install goals.
# The audit requires the whole project even when all was not requested.
GOALS       := $(if $(MAKECMDGOALS),$(MAKECMDGOALS),all)
BUILD_GOALS := $(filter-out check clean regen layers,$(GOALS))
ifneq ($(filter check,$(GOALS)),)
ifeq ($(filter all,$(BUILD_GOALS)),)
BUILD_GOALS := all $(BUILD_GOALS)
endif
endif
DELEGATED := $(filter-out all,$(BUILD_GOALS))

.PHONY: delegate
delegate: regen
	$(MAKE) -f $(COQMAKEFILE) $(BUILD_GOALS)

ifneq ($(filter clean,$(GOALS)),)
ifneq ($(strip $(BUILD_GOALS)),)
delegate: clean
endif
endif

ifneq ($(strip $(DELEGATED)),)
$(DELEGATED): delegate
endif
