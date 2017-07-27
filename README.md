# iRRAM-coq: Hoare logic for iRRAM in Coq

This repository contains the Coq development of a Hoare logic for **iRRAM** for
supporting fearless verification.

## Dependencies

The master branch is known to compile with:
* [coq] 8.6
* [ssreflect] 1.6.1
* [iris] 3.0

## Build

The recommended way to build the development is using OPAM. To avoid conflicts
with existing packages, we recommend to create a new opam switch:

```sh
opam switch iRRAM-coq --alias-of=4.04.0
```

It should work for any compiler version upwards of 4.04.0. After compiling
OCaml, the new switch needs to be activated in your current shell. opam will
print the necessary instructions.

To find all the dependencies of iRRAM-coq, opam needs to know about the Coq opam
archive. This can be achieved by executing:

```sh
opam repo add coq-released https://coq.inria.fr/opam/released
```

Now, execute `make dep` to install all dependencies of iRRAM-coq. Finally,
execute `make` to quickly compile the development, and `make build` for fully
build the development.

## Run ilog2

```sh
./run_ilog2.sh
```


[coq]: https://coq.inria.fr/
[ssreflect]: https://math-comp.github.io/math-comp/
[iris]: https://gitlab.mpi-sws.org/FP/iris-coq
