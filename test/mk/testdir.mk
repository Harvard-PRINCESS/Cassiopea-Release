#
# Run tests
#
# To use: set TESTTYPE, TESTS, and (where necessary) CASPFILE.
#
# TESTTYPE should be one of:
#    parser interp verify synth extract
#
# TESTS should be a list of test basenames (without extensions)
#
# CASPFILE should be the name of the machine spec to use.
# CASPFILE.$(TEST) can be used to override this for individual tests.
#
# The test types:
#   parser:
#	read in $(TEST).casp, typecheck, dump out
#
#   interp:
#	using $(CASPFILE).casp, interpret $(TEST).prog
#
#   symexec:
#	using $(CASPFILE).casp, symbolically $(TEST).prog
#
#   verify:
#	using $(CASPFILE).casp, verify $(TEST).prog against $(TEST).spec
#
#   synth:
#	using $(CASPFILE).casp, synthesize for $(TEST).spec
#       
#   extract:
#	using $(CASPFILE).casp, extract asm for $(TEST).prog
#
# Note that for verify, synth, and extract, the output appears in
# $(TEST).out, regardless of what kind of file it is. This allows
# keeping a clear distinction between test inputs and test outputs.
#

# Determine whether we expect an .out file to appear
.if $(TESTTYPE) == "verify" || $(TESTTYPE) == "synth" || $(TESTTYPE) == "extract"
HASOUTPUT=# defined
.endif

# primary rule: run tests first, print all the diffs afterwards
# (this split occurs at all makefile levels and is crucial for a
# pleasant testing experience) 
all: run-tests .WAIT show-diffs

# for all tests...
.for T in $(TESTS)

# The default .casp file for this test is the globally set one
CASPFILE.$(T)?=$(CASPFILE)

# the test product is the diff (not just the logs and output)
run-tests: $(T).log.diff
.if defined(HASOUTPUT)
run-tests: $(T).out.diff	# also diff the .out file
.endif

# The outputs always depend on casp itself
$(T).log $(T).out: $(CASP)

#
# Run the test
#

.if $(TESTTYPE) == "parser"
$(T).log: $(T).casp
	$(CASP) -v $(T).casp > $@ 2>&1 || echo FAILED >> $@

.elif $(TESTTYPE) == "interp"
$(T).log: $(CASPFILE.$(T)) $(T).prog $(T).init
	$(CASP) $(CASPFILE.$(T)) -interp $(T).prog $(T).init > $@ 2>&1 || \
		echo FAILED >> $@

.elif $(TESTTYPE) == "symexec"
$(T).log: $(CASPFILE.$(T)) $(T).prog
	$(CASP) $(SOLVERFLAGS) $(CASPFILE.$(T)) -sequence +coninit rand +dup +concrete $(T).prog +swap +syminit +symbolic $(T).prog +substitute +assertconeq > $@ 2>&1 && \
	$(CASP) $(SOLVERFLAGS) $(CASPFILE.$(T)) -sequence +coninit rand +dup +concrete $(T).prog +swap +syminit +symbolic $(T).prog +substitute +assertconeq >> $@ 2>&1 && \
	$(CASP) $(SOLVERFLAGS) $(CASPFILE.$(T)) -sequence +coninit rand +dup +concrete $(T).prog +swap +syminit +symbolic $(T).prog +substitute +assertconeq >> $@ 2>&1 || \
		echo FAILED >> $@

.elif $(TESTTYPE) == "verify"
$(T).log $(T).out: $(CASPFILE.$(T)) $(T).spec $(T).prog
	$(CASP) -l $(T).log.raw $(SOLVERFLAGS) $(CASPFILE.$(T)) \
		-verify $(T).spec $(T).prog -o $(T).out ||\
	   echo FAILED >> $(T).log.raw
	sed '/Time/s/[0-9.][0-9.]*s/???s/' < $(T).log.raw > $(T).log

.elif $(TESTTYPE) == "synth"
$(T).log $(T).out: $(CASPFILE.$(T)) $(T).spec
	$(CASP) -l $(T).log.raw $(SOLVERFLAGS) $(CASPFILE.$(T)) \
		-synth $(T).spec -o $(T).out || \
	   echo FAILED >> $(T).log.raw
	sed '/Time/s/[0-9.][0-9.]*s/???s/' < $(T).log.raw > $(T).log

.elif $(TESTTYPE) == "extract"
$(T).log $(T).out: $(CASPFILE.$(T)) $(T).prog
	$(CASP) $(SOLVERFLAGS) $(CASPFILE.$(T)) -extract $(T).prog -o $(T).out > $(T).log 2>&1 || \
		echo FAILED >> $(T).log

.else
.error "Invalid TESTTYPE $(TESTTYPE)"
.endif

# XXX: bmake does not parallelize properly when one rule produces two
# outputs (long-standing complex issue with no agreement on a
# solution) so make the second output appear to depend on the first.
$(T).out: $(T).log

#
# Diff the output
#

$(T).log.diff: $(T).log.good $(T).log
	diff -u $(T).log.good $(T).log > $@ || true

$(T).out.diff: $(T).out.good $(T).out
	diff -u $(T).out.good $(T).out > $@ || true

.endfor # TESTS

#
# Print the diffs
#
show-diffs:
.for T in $(TESTS)
	@cat $(T).log.diff
.if defined(HASOUTPUT)
	@cat $(T).out.diff
.endif
.endfor

#
# Check for nonempty diffs
#
check-diffs:
.for T in $(TESTS)
	@if [ -s $(T).log.diff ]; then echo "Test diffs for $(T).log"; false; fi
.if defined(HASOUTPUT)
	@if [ -s $(T).log.diff ]; then echo "Test diffs for $(T).out"; false; fi
.endif
.endfor

#
# Update the .good files
#
good:
.for T in $(TESTS)
	cp $(T).log $(T).log.good
.if defined(HASOUTPUT)
	cp $(T).out $(T).out.good
.endif
.endfor

#
# Clean up
#
clean:
	rm -f *.log *.out *.log.raw *.out.raw *.diff

.PHONY: all run-tests show-diffs check-diffs good clean
