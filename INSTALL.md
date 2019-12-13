# Dependencies

OCaml version 4.06.x
BSD make (bmake in linux distribu†ions, used for running tests)

{macos}
```
brew install bmake
brew install ocaml
brew install opam
opam init
eval `opam config env`
```

{ubuntu 18.04}
```
apt-get install bmake
apt-get install opam
apt-get install m4
opam init
eval `opam config env`
opam switch 4.06.0
#just start a new shell at this point
```

{both, once opam is installed and the appropriate switch is active}
```
opam install ocamlbuild
opam install ocamlfind
opam install num
opam install menhir
opam install batteries
```

{pkgsrc on netbsd, solaris, etc.}
```
pkgin install ocaml ocaml-findlib ocamlbuild ocaml-num menhir
```

{ubuntu 18.04}
```
eval `opam config env`
```
{macos}
```
eval $(opam env)
```

# Building

* `make` to build
* `make clean` to clean up after ocamlbuild

# Running

`./cassiopeia examples/[desired example].casp`

# Verification and Synthesis

For verification and synthesis, Cassiopea expects an SMT solver in {boolector,Z3,yices} to be
in your path. We recommend boolector or yices for performance or Z3 for ease of installation

## boolector download

    # Download and build Boolector
    git clone https://github.com/boolector/boolector
    cd boolector

    # Download and build Lingeling
    ./contrib/setup-lingeling.sh

    # Download and build BTOR2Tools
    ./contrib/setup-btor2tools.sh

    # Build Boolector and install
    ./configure.sh && cd build && make && sudo make install

## Z3

Ubuntu:

sudo apt-get install z3

Macos:

brew install z3

Others:

source is available at:

https://github.com/Z3Prover/z3

## yices

We recommend building v2.6.2 from source

https://github.com/SRI-CSL/yices2

You will need to perform a make install to yield the correct linked binary names (Cassiopea expects yices-mt2)

Yices support is currently considered to be experimental
