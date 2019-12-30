.SUFFIXES: .v .vo

all: support.vo

.v.vo:
	coqc $<

clean:
	rm -f *.vo *.glob .*.aux
