#!/usr/bin/env bash

make build

cd ocaml
ocamlbuild -use-ocamlfind -I extraction 'ilog2_print.native'
./ilog2_print.native > ../c++/ilog2.cc
cd ..

cd c++
g++ -std=c++11 -g -I/Users/jeehoon/Works/iRRAM/installed/include -Xlinker -rpath -Xlinker /Users/jeehoon/Works/iRRAM/installed/lib  ilog2-main.cc ilog2.cc  -L/Users/jeehoon/Works/iRRAM/installed/lib -liRRAM -lmpfr -lgmp -lm -lpthread -o ilog2
./ilog2
cd ..
