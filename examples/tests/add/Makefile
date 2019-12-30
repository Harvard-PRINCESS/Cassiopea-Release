%.prog: ../../../cassiopeia mips.casp %.spec
	../../../cassiopeia --no-branch --whiten solver mips.casp -synth $*.spec -o $*.prog -l $*.log

all: add2.prog add3.prog add4.prog add5.prog

clean:
	rm -f *.prog
	rm -f *.log

.PHONY: all clean
