#!/usr/bin/env bash

make build

cd ocaml
ocamlbuild -use-ocamlfind -I extraction 'ilog2_print.native'
./ilog2_print.native > ../c++/ilog.cc
cd ..
