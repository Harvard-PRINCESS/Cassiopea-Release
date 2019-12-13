# Languages
* *Alewife* - A language for expressing machine-independent specifications of OS
  functionality
* *Cassiopeia* - A metalanguage for describing the semantics of an assembly
  language and machine architecture as it relates to the operations of an OS.

# Anchor: The Alewife Compiler
A compiler that translates machine-independent (MI) specifications written in
Alewife into machine-dependent (MD) specifications written in Cassiopeia.

## Usage
```
./alewife [ale] [casp] [map] [-o spec]
```

## Input File Types
 * [ale] : MI specification
 * [casp] : machine description
 * [map] : MI-to-MD lowering declarations

## Output File Type (`-o`)
 * [spec] : MD specification

## Example

To produce a machine specification instance for the barrelfish "get_disp" use case:

```
cd example/usecase_barrelfish/get_disp
../../../alewife ale.ale ../../usecase_machines/arm32.casp ../mapping-arm32.casp -o out.spec
cat out.spec
```

# Capstan: The Cassiopea interpreter, verifier and synthesizer

# Synthesis Engine
An interpreter, symbolic execution, and synthesis engine that takes a
Cassiopeia machine description and an MD specification instance (from Alewife)
and produces an assembly program.

## Input File Types
 * [casp] : machine description
 * [prog] : list of operations (machine instructions)
 * [init] : initial machine state (including registers and memory)
 * [spec] : MD specification

## Usage
Invoke cassiopeia with the `-help` flag to get the following output:
```
Usage: ./cassiopeia [command] casp [files...] [options...]
       [command] := -interp | -verify | -synth | -sketch | -deduce |-extract

Cassiopeia accepts a command indicating what action it should perform.
A command might expect some files. The accepted file types are as follows:
 * prog : files containing a list of instructions
 * spec : files containing pre-/post-condition specs
The following describes flags and possible commands with their expected arguments:
  -interp [prog] [init]: interpret [prog] on starting state [init]
  -verify [spec] [prog]: verify [prog] against [spec]
  -synth [spec]: synthesize prog from [spec]
  -sketch [spec] [sketch]: synthesize prog from [spec] with [sketch]
  -deduce [spec] : synthesize prog from [spec]
  -extract [prog] : extract ASM from [prog]
  -bitsize : show approximate per-instruction search space size
  -o : set file for result output
  -l : set file for logging
  -smt : set file for smtlib dump
  -sv : print synthesis details
  --debug : enable debug logging mode
  --dump-interp : dump interpreter function calls
  --dump-solver : dump solver interaction
  --dry-run : cause CEGIS to always fail
  --max-insts : maximum instructions (default 4)
  --bucketed : synthesis with counter-example bucketing
  --accumulation : synthesis with candidate accumulation
  --sorting : synthesis with assembly instruction sorting
  --weak-coerce : use weaker coercion
  --no-unify : disable equality unification for specifications
  --no-branch : disable branching
  --use-cex-solver : set verification solver (z3, btor, yices) (z3 by default)
  --use-syn-solver : set synthesis solver (z3, btor, yices) (btor by default)
  --seed : set random seed for whitening and SMT solver
  --whiten : whiten [solver, logic, insts, args]
  -help  Display this list of options
  --help  Display this list of options
```

* Synth

Given a .spec file, a .prog file, and the corresponding machine description
(.casp file), produce an implementation .prog file that satisfies the .spec
file.

* Verify

Given a .spec file, a .prog file and the corresponding machine description
(.casp file), verify that the .prog file implements the .spec file.

* Interp

Given .prog file and the corresponding machine description (.casp file),
execute the program. More details are available in the accompanying tech report.

* Deduce

Use an experimental rule-based decomposition algorithm to solve a large use
case as multiple smaller synthesis problems.

* Extract

Extract assembly code from a .prog file (see *running use cases* below).

## Running tests

```
cd test
bmake
```

You will see a report of differences, if any, with expected output.
Some outputs are out of date; differences in instruction order or execution
time output don't indicate anything amiss.

## Running use cases

*Experimental!*

All
```
cd examples/
bmake
```

OS161
```
cd examples/usecase_os161/
bmake
````

Barrelfish
```
cd examples/usecase_barrelfish/
bmake
```

Example output
```
$ bmake
(cd initial_stack && bmake all)
(cd get_disp && bmake all)
../../../cassiopeia  ../../usecase_machines/mips.casp -synth spec-mips.spec -o synth-mips.prog -l synth-mips.log
../../../cassiopeia  ../../usecase_machines/mips.casp -verify spec-mips.spec synth-mips.prog -o verify-synth-mips.out -l verify-synth-mips.log || echo FAILED >> verify-synth-mips.out
```

```
$ cd get_disp
$ cat verify-synth-mips.out
succeeded
$ cat synth-mips.prog
(LW r28 r4 0b0000000000000000)
(LW r28 r28 0b0000000000000000)
(LW r28 r28 0b0000000000001000)
$ ../../../cassiopeia -extract ../../usecase_machines/mips.casp synth-mips.prog
Command: Extract ASM from synth-mips.prog and output to <stdout>, log to <stdout>
lw $gp, 0($4)
lw $gp, 0($gp)
lw $gp, 8($gp)
	Execution Time: 0.005102s
```

# IMPORTANT!
Depending on the performance of z3 on your machine, expect a full run to take between 3 and ?? hours.

## Contact:

Feedback, issues, etc. to ming@seas.harvard.edu
