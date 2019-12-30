#
# Base definitions for regression test makefiles
#

CASP=$(TOP)/../cassiopeia
#SOLVERFLAGS+=--no-boolector
#SOLVERFLAGS+=--no-z3

# you can put your own local settings in here
# (top of the test/ tree)
.-include "$(TOP)/defs.mk"
