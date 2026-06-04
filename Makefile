COQPROJECT := _CoqProject
COQMAKEFILE := CoqMakefile
VC_TARGETS := \
	convex-hull/ConvexHull/point_array_strategy_proof.vo \
	convex-hull/ConvexHull/safeexec_strategy_proof.vo \
	convex-hull/ConvexHull/graham_scan_proof_auto.vo \
	convex-hull/ConvexHull/graham_scan_proof_manual.vo \
	convex-hull/ConvexHull/graham_scan_goal_check.vo

.DEFAULT_GOAL := build

.PHONY: all build all-vfiles clean distclean deps

all: build

build: deps
	$(MAKE) -f $(COQMAKEFILE) $(VC_TARGETS)

all-vfiles: deps
	$(MAKE) -f $(COQMAKEFILE)

clean: deps
	$(MAKE) -f $(COQMAKEFILE) clean

distclean:
	@if [ -f "$(COQMAKEFILE)" ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	$(RM) $(COQMAKEFILE) $(COQMAKEFILE).conf .$(COQMAKEFILE).d

deps: $(COQMAKEFILE)

$(COQMAKEFILE): $(COQPROJECT)
	coq_makefile -f $(COQPROJECT) -o $(COQMAKEFILE)
