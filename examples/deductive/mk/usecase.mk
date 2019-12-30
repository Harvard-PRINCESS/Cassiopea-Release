#
# For each use case we want to be able to do the following:
#
# - generate the spec file
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
#    verify-hand-$(MACHINE).out
#    verify-synth-$(MACHINE).out
#

MAPPINGDIR?=..

all: verify
specs: ;
synth: ;
verify-hand: ;
verify-synth: ;
verify: verify-hand verify-synth extract
extract: ;
fast: specs verify-hand

.for M in $(MACHINES)
$(M): verify-$(M)
all-$(M): $(M)
specs-$(M): ;
synth-$(M): ;
verify-hand-$(M): ;
verify-synth-$(M): ;
verify-$(M): verify-hand-$(M) verify-synth-$(M) extract-$(M)
extract-$(M): ;
$(M)-fast: specs-$(M) inter-hand-$(M) verify-hand-$(M)
.endfor

.for M in $(MACHINES)
specs specs-$(M): spec-$(M).spec
spec-$(M).spec: $(ALE) $(MACHINEDIR)/$(M).casp $(MAPPINGDIR)/mapping-$(M).casp ale.ale
	$(ALE) ale.ale $(MACHINEDIR)/$(M).casp $(MAPPINGDIR)/mapping-$(M).casp -o $@

synth synth-$(M): synth-$(M).prog
synth-$(M).prog: $(CASP) spec-$(M).spec
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -synth spec-$(M).spec -o $@ -l synth-$(M).log
synth-$(M).log: synth-$(M).out
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

extract extract-$(M): extract-synth-$(M).asm
extract-synth-$(M).asm: $(CASP) synth-$(M).prog
	$(CASP) $(CASPFLAGS) $(MACHINEDIR)/$(M).casp -extract synth-$(M).prog -o $@ -l extract-synth-$(M).log || echo FAILED >> $@
extract-synth-$(M).log: extract-synth-$(M).asm
	@true

.endfor # MACHINES

clean:
	rm -f spec-*.spec synth-*.prog *.log *.out extract-*.asm

.PHONY: all specs synth verify-hand verify-synth verify extract fast clean
.for M in $(MACHINES)
.PHONY: $(M) specs-$(M) synth-$(M) verify-hand-$(M) verify-synth-$(M)
.PHONY: verify-$(M) extract-$(M) fast-$(M)
.endfor
