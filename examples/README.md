Everything in here is supposed to work, or at least run and then take forever.

Stuff intended as test cases are in tests/.

# Usecases

The material for the PLDI paper is in the usecase\* directories:
* `usecase_barrelfish` has the cases taken from Barrelfish.
* `usecase_os161` has the cases taken from OS/161.
* `usecase_machines` holds the machine description files.

Barrelfish use cases are:
* `usecase_barrelfish/disp_disabled`
* `usecase_barrelfish/check_low`
* `usecase_barrelfish/check_high`
* `usecase_barrelfish/set_area`
* `usecase_barrelfish/get_disp`
* `usecase_barrelfish/find_got`

OS/161 use cases are:
* `usecase_os161/cpu_irqoff`
* `usecase_os161/crt0_initregs`
* `usecase_os161/crt0_savevals`
* `usecase_os161/setjmp-ret`
* `usecase_os161/setjmp-full`
* `usecase_os161/longjmp-ret`
* `usecase_os161/longjmp-full`
* `usecase_os161/syscalls_loadnum`

## Automatic Evaluation
From the top level:
* Run `bmake` to get everything.
* Run `bmake clean` to remove outputs.
* Run `bmake fast` to get only verify-hand and interp-hand.
* Run `bmake verify-hand` to verify handwritten code.
* Run `bmake interp-hand` to interpret handwritten code.
* Run `bmake synth` for synthesis.

If you want to restrict the set of machines for barrelfish or os161 use cases,
modify the `MACHINES` variable in the appropriate subdirectory's `common.mk`.

From a use case directory:
* Run `bmake [command]-[machine]` to get results for a single machine.
  For instance, run `bmake synth-arm32` to run synthesis with the arm32 machine only.

## Manual Evaluation
To evaluate manually: 1. go to a use case folder; 2. execute the following commands.

### arch: arm32
```
# interpreter
../../../cassiopeia ../../usecase_machines/arm32.casp -interp hand-arm32.prog init-arm32.init
# alewife
../../../alewife ale.ale ../../usecase_machines/arm32.casp ../mapping-arm32.casp -o spec-arm32.spec
# synth
../../../cassiopeia ../../usecase_machines/arm32.casp -synth spec-arm32.spec
# verify handwritten
../../../cassiopeia ../../usecase_machines/arm32.casp -verify spec-arm32.spec hand-arm32.prog
```
### arch: amd64
```
# interpreter
../../../cassiopeia ../../usecase_machines/amd64.casp -interp hand-amd64.prog init-amd64.init
# alewife
../../../alewife ale.ale ../../usecase_machines/amd64.casp ../mapping-amd64.casp -o spec-amd64.spec
# synth
../../../cassiopeia ../../usecase_machines/amd64.casp -synth spec-amd64.spec
# verify handwritten
../../../cassiopeia ../../usecase_machines/amd64.casp -verify spec-amd64.spec hand-amd64.prog
```
### arch: mips (full version)
```
## interpreter
../../../cassiopeia ../../usecase_machines/mips.casp -interp hand-mips.prog init-mips.init
## alewife
../../../alewife ale.ale ../../usecase_machines/mips.casp ../mapping-mips.casp -o spec-mips.spec
## synth
../../../cassiopeia ../../usecase_machines/mips.casp -synth spec-mips.spec
## verify handwritten
../../../cassiopeia ../../usecase_machines/mips.casp -verify spec-mips.spec hand-mips.prog
```

### arch: mips (small version)
```
# interpreter
../../../cassiopeia ../../usecase_machines/mipssmall.casp -interp hand-mipssmall.prog init-mipssmall.init
# alewife
../../../alewife ale.ale ../../usecase_machines/mipssmall.casp ../mapping-mipssmall.casp -o spec-mipssmall.spec
# synth
../../../cassiopeia ../../usecase_machines/mipssmall.casp -synth spec-mipssmall.spec
# verify handwritten
../../../cassiopeia ../../usecase_machines/mipssmall.casp -verify spec-mipssmall.spec hand-mipssmall.prog
```
