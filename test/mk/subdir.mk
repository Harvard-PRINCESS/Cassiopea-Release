#
# recurse into subdirs
#
# To use: set SUBDIRS
#

# these targets should parallelize
TARGETS_PAR=run-tests good check-diffs clean
# show-diffs should not parallelize
TARGETS_SEQ=show-diffs

# divide phases
all: run-tests .WAIT show-diffs

$(TARGETS_PAR): ;

.for T in $(TARGETS_PAR)
.for D in $(SUBDIRS)
$(T): $(T)-$(D)
$(T)-$(D):
	(cd $(D) && $(MAKE) $(T))
.PHONY: $(T)-$(D)
.endfor
.PHONY: $(T)
.endfor

.for T in $(TARGETS_SEQ)
$(T):
.for D in $(SUBDIRS)
	(cd $(D) && $(MAKE) $(T))
.endfor
.PHONY: $(T)
.endfor

.PHONY: all
