SMT2COQ=../../../smt2coq

TESTS=t1 smt t2 caspdump

all: run-tests .WAIT show-diffs

run-tests: ;
.for TEST SUFF in $(TESTS)
run-tests: $(TEST).diff
$(TEST).diff: $(TEST).good $(TEST).v
	@diff -u $(TEST).good $(TEST).v > $@ || true
$(TEST).v: $(TEST).$(SUFF) $(SMT2COQ)
	$(SMT2COQ) $(SUFF:Mcaspdump:C/.+/-c/) $(TEST).$(SUFF) >$@ 2>&1 || \
		echo FAILED >> $@
.endfor

show-diffs:
.for TEST SUFF in $(TESTS)
	@cat $(TEST).diff
.endfor

good:
.for TEST SUFF in $(TESTS)
	mv $(TEST).v $(TEST).good
.endfor

clean distclean:
	rm -f *.v *.diff

.PHONY: all run-tests show-diffs good clean distclean
