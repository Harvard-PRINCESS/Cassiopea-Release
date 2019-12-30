RULES?=\
	all fast \
	specs synth interp-hand interp-synth verify-hand verify-synth verify extract \
	clean

$(RULES): ;
.for D in $(SUBDIRS)
.for R in $(RULES)
.if $(D) == ".WAIT"
$(R): .WAIT
.else
$(R): $(D)-$(R)
$(D)-$(R):
	(cd $(D) && $(MAKE) $(R))
.PHONY: $(D)-$(R)

.if defined(MACHINES)
.for M in $(MACHINES)
$(R)-$(M): $(D)-$(R)-$(M)
$(D)-$(R)-$(M):
	(cd $(D) && $(MAKE) $(R)-$(M))
.PHONY: $(D)-$(R)-$(M)
.endfor
.endif

.endif
.endfor
.endfor

.if defined(MACHINES)
.for M in $(MACHINES)
$(M): all-$(M)
.for R in $(RULES)
.PHONY: $(R)-$(M)
.endfor
.endfor
.endif

.PHONY: $(RULES)
