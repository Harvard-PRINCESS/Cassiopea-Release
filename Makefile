CASP_DIR=src/tools/cassiopeia
ALE_DIR=src/tools/alewife
NAUT_DIR=src/tools/nautilus
SMT2COQ_DIR=src/tools/smt2coq

# replace "cassiopeia.native" with "cassiopeia.byte" to use ocamldebug
BYTE_CASP=cassiopeia.native
BYTE_ALE=alewife.native
BYTE_NAUT=nautilus.native
BYTE_SMT2COQ=smt2coq.native

# replace "-tag debug" with "-tag profile" to use gprof
FLAGS=\
	-use-ocamlfind \
	-tag debug -tag safe_string \
	-tag warn\(A-4-9+27-33-40-42-44-45-60\) \
	-tag warn_error\(A\) \
	-tag dtypes -tag annot \
	-use-menhir -menhir 'menhir --explain --table'

INCLUDES=\
  -I src/util \
  -I src/casplib \
  -I src/interpret \
  -I src/symbolic/base \
  -I src/symbolic/term \
  -I src/symbolic/vars \
  -I src/symbolic/exec \
  -I src/solver \
  -I src/analyze \
  -I src/query \
  -I src/sygus \
  -I src/deduce

all: cassiopeia alewife nautilus smt2coq

cassiopeia: FORCE
	@echo "        [OCAMLBUILD] $@"
	@ocamlbuild $(INCLUDES) $(FLAGS) $(CASP_DIR)/$(BYTE_CASP)
	mv -f $(BYTE_CASP) cassiopeia

alewife: FORCE
	@echo "        [OCAMLBUILD] $@"
	@ocamlbuild $(INCLUDES) $(FLAGS) $(ALE_DIR)/$(BYTE_ALE)
	mv -f $(BYTE_ALE) alewife

nautilus: FORCE
	@echo "        [OCAMLBUILD] $@"
	@ocamlbuild $(FLAGS) $(NAUT_DIR)/$(BYTE_NAUT)
	mv -f $(BYTE_NAUT) nautilus

smt2coq: FORCE
	@echo "        [OCAMLBUILD] $@"
	@ocamlbuild $(FLAGS) $(SMT2COQ_DIR)/$(BYTE_SMT2COQ)
	mv -f $(BYTE_SMT2COQ) smt2coq

install: cassiopeia alewife nautilus
	echo -n "install does nothing. sorry :("

test:
	cd test && $(MAKE) && $(MAKE) check-diffs && cd ../examples && $(MAKE)

clean:
	rm -f $(ML_GEN_ML) cassiopeia alewife nautilus smt2coq
	rm -rf _build

distclean: clean

FORCE:

.PHONY: all depend test clean distclean FORCE

