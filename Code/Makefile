# Maintained build entry point for the Coq development.
#
# Every invocation first regenerates Makefile.coq from _CoqProject with
# coq_makefile and then delegates the requested goals to it, so edits to
# _CoqProject take effect without a manual regeneration step.  Makefile.coq,
# Makefile.coq.conf, and the .*.d dependency files are generated artifacts
# (see .gitignore); this wrapper is the committed interface.
#
#   make                     build everything (default; no assumption reports)
#   make check               opt-in audit: build prerequisites, print assumptions
#   make clean               delegate clean and also remove the audit's outputs
#   make GOAL...             any other goal passes through to Makefile.coq
#                             (file targets like Classes/Arrow.vo, install, ...)
#
# Parallel builds (make -jN) and multiple goals are forwarded to a single
# sub-make through the jobserver, so shared prerequisites are never built
# concurrently by two sub-makes.

COQ_MAKEFILE ?= coq_makefile
COQPROJECT   := _CoqProject
COQMAKEFILE  := Makefile.coq
COQC         ?= coqc
COQDEBUG     ?=
COQFLAGS     ?= -q
COQLIBS      := -Q . Incorrectness

.DEFAULT_GOAL := all

.PHONY: regen
regen:
	$(COQ_MAKEFILE) -f $(COQPROJECT) -o $(COQMAKEFILE)

.PHONY: all
all: regen
	$(MAKE) -f $(COQMAKEFILE) all

# The audit is deliberately outside _CoqProject, so the normal build never
# compiles it and the generated clean rule never removes its outputs.
CHECK_VOS := Classes/RelArrowCoherence.vo \
  Taxonomy/Arrows/SPostArrMonad.vo \
  Taxonomy/Arrows/GaloisArr.vo \
  Taxonomy/EffectObservations/SP/StExcNonDet_SPostArr.vo \
  Taxonomy/EffectObservations/SP/StDivNonDet_SPostArr.vo \
  Taxonomy/EffectObservations/SP/StDivITree_SPostArr.vo \
  Taxonomy/EffectObservations/SP/StDivExcNonDet_SPostArr.vo \
  Taxonomy/BaseSpecMonads/SPBindOrderCounterexample.vo

.PHONY: check
check: regen
	$(MAKE) -f $(COQMAKEFILE) $(CHECK_VOS)
	$(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) Checks/Assumptions.v

.PHONY: clean
clean: regen
	$(MAKE) -f $(COQMAKEFILE) clean
	rm -f Checks/Assumptions.vo Checks/Assumptions.vos Checks/Assumptions.vok \
	  Checks/Assumptions.glob Checks/.Assumptions.aux

# Pass every other goal through to the generated makefile.  All such goals
# are funneled into one sub-make invocation; the empty per-goal recipes only
# mark them as (re)made after that sub-make has succeeded.
GOALS     := $(if $(MAKECMDGOALS),$(MAKECMDGOALS),all)
DELEGATED := $(filter-out all check clean regen,$(GOALS))

.PHONY: delegate
delegate: regen
	$(MAKE) -f $(COQMAKEFILE) $(DELEGATED)

ifneq ($(strip $(DELEGATED)),)
$(DELEGATED): delegate
endif
