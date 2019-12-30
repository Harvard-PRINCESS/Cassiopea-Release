#
# For each use case we want to be able to do the following:
#
# - generate the spec file
# - interpret the handwritten assembly
# - verify the handwritten assembly
# - synthesize
# - verify the synthesis output
#
# and for synthesis and verification steps we also want to record timings
# over multiple trials, but I guess we'll not do that just yet.
#
# The files are:
#    ale.ale
#    init-$(MACHINE).init
#    hand-$(MACHINE).prog
#    spec-$(MACHINE).spec
#    synth-$(MACHINE).prog
#    synth-$(MACHINE).log
#    interp-hand-$(MACHINE).out
#    interp-synth-$(MACHINE).out
#    verify-hand-$(MACHINE).out
#    verify-synth-$(MACHINE).out
#

MAPPINGDIR?=..

all: verify
specs: ;
synth: ;
deduce: ;
interp-hand: ;
interp-synth: ;
verify-hand: ;
verify-synth: ;
verify-deduce: ;
extract-synth: ;
extract-deduce: ;
verify: verify-hand verify-synth extract-synth
deduceall: verify-hand verify-deduce extract-deduce
fast: specs interp-hand verify-hand

.for M in $(MACHINES)
$(M): verify-$(M)
all-$(M): $(M)
specs-$(M): ;
synth-$(M): ;
deduce-$(M): ;
interp-hand-$(M): ;
interp-synth-$(M): ;
interp-deduce-$(M): ;
verify-hand-$(M): ;
verify-synth-$(M): ;
extract-synth-$(M): ;
extract-deduce-$(M): ;
verify-$(M): verify-hand-$(M) verify-synth-$(M) extract-synth-$(M)
deduceall-$(M): verify-hand-$(M) verify-deduce-$(M) extract-deduce-$(M)
$(M)-fast: specs-$(M) inter-hand-$(M) verify-hand-$(M)
.endfor

.for M in $(MACHINES)
specs specs-$(M): spec-$(M).spec
spec-$(M).spec: $(ALE) $(MACHINEDIR)/$(M).casp $(MAPPINGDIR)/mapping-$(M).casp ale.ale
	$(ALE) ale.ale $(MACHINEDIR)/$(M).casp $(MAPPINGDIR)/mapping-$(M).casp -o $@

synth synth-$(M): synth-$(M).prog
synth-$(M).prog: $(CASP) spec-$(M).spec
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -synth spec-$(M).spec -o $@ -l synth-$(M).log --use-cex-solver z3 --use-syn-solver z3
synth-$(M).log: synth-$(M).out
	@true

deduce deduce-$(M): deduce-$(M).prog
deduce-$(M).prog: $(CASP) spec-$(M).spec
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -deduce spec-$(M).spec -o $@ -l deduce-$(M).log  --use-syn-solver z3
deduce-$(M).log: deduce-$(M).out
	@true

interp-hand inter-hand-$(M): interp-hand-$(M).out
interp-hand-$(M).out: $(CASP) $(MACHINEDIR)/$(M).casp hand-$(M).prog init-$(M).init 
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -interp hand-$(M).prog init-$(M).init -o $@ -l interp-hand-$(M).log
interp-hand-$(M).log: interp-hand-$(M).out
	@true

interp-synth interp-synth-$(M): interp-synth-$(M).out
interp-synth-$(M).out: $(CASP) $(MACHINEDIR)/$(M).casp synth-$(M).prog init-$(M).init 
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -interp synth-$(M).prog init-$(M).init -o $@ -l interp-synth-$(M).log || echo '(FAIL)' >> $@
interp-synth-$(M).log: interp-synth-$(M).out
	@true

verify-hand verify-hand-$(M): verify-hand-$(M).out verify-hand-$(M).log
verify-hand-$(M).out: $(CASP) spec-$(M).spec hand-$(M).prog
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -verify spec-$(M).spec hand-$(M).prog -o $@ -l verify-hand-$(M).log || echo FAILED >> $@
verify-hand-$(M).log: verify-hand-$(M).out
	@true

verify-synth verify-synth-$(M): verify-synth-$(M).out
verify-synth-$(M).out: $(CASP) spec-$(M).spec synth-$(M).prog
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -verify spec-$(M).spec synth-$(M).prog -o $@ -l verify-synth-$(M).log || echo FAILED >> $@
verify-synth-$(M).log: verify-synth-$(M).out
	@true

verify-deduce verify-deduce-$(M): verify-deduce-$(M).out
verify-deduce-$(M).out: $(CASP) spec-$(M).spec deduce-$(M).prog
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -verify spec-$(M).spec deduce-$(M).prog -o $@ -l verify-deduce-$(M).log || echo FAILED >> $@
verify-deduce-$(M).log: verify-deduce-$(M).out
	@true

extract-synth extract-synth-$(M): extract-synth-$(M).asm
extract-synth-$(M).asm: $(CASP) synth-$(M).prog
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -extract synth-$(M).prog -o $@ -l extract-synth-$(M).log || echo FAILED >> $@
extract-synth-$(M).log: extract-synth-$(M).asm
	@true

extract-deduce extract-deduce-$(M): extract-deduce-$(M).asm
extract-deduce-$(M).asm: $(CASP) deduce-$(M).prog
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -extract deduce-$(M).prog -o $@ -l extract-deduce-$(M).log || echo FAILED >> $@
extract-deduce-$(M).log: extract-deduce-$(M).asm
	@true

.endfor # MACHINES

clean:
	rm -f spec-*.spec synth-*.prog deduce-*.prog *.log *.out extract-*.asm

.PHONY: all specs synth deduce verify-hand verify-synth verify-deduce verify deduceall extract-synth extract-deduce fast clean
.for M in $(MACHINES)
.PHONY: $(M) specs-$(M) synth-$(M) deduce-$(M) verify-hand-$(M) verify-synth-$(M) verify-deduce-$(M) extract-synth-$(M) extract-deduce-$(M)
.PHONY: verify-$(M) deduceall-$(M) fast-$(M)
.endfor
