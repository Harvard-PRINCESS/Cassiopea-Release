CASP=../../cassiopeia
ALE=../../alewife

INSANITY=./insanity
CASP_DIR=./casp
SPEC_DIR=./spec

mkdir:
	rm -rf $(SPEC_DIR) && \
	mkdir -p $(SPEC_DIR)

clean:
	rm -rf $(SPEC_DIR)
	
ale:
	$(ALE) $(INSANITY)/ptr5.ale $(CASP_DIR)/map-5reg.casp -o $(SPEC_DIR)/ptr5.spec

deduce:
	time $(CASP) $(CASP_DIR)/arm-flag-5reg.casp -deduce $(SPEC_DIR)/ptr5.spec

CASP=time ../../../cassiopeia
ALE=../../../alewife

ale:
	$(ALE) noptr.ale map.casp -o noptr.spec
	$(ALE) ldr.ale map.casp -o ldr.spec
	$(ALE) str.ale map.casp -o str.spec

verify: 
	$(CASP) small.casp -verify noptr.spec noptr.prog
	$(CASP) small.casp -verify ldr.spec ldr.prog
	$(CASP) small.casp -verify str.spec str.prog

synth: 
	$(CASP) small.casp -synth noptr.spec
	$(CASP) small.casp -synth ldr.spec
	$(CASP) small.casp -synth str.spec

interp:
	$(CASP) small.casp -interp noptr.prog
	$(CASP) small.casp -interp ldr.prog
	$(CASP) small.casp -interp str.prog
