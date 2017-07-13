COQMODULE    := iRRAM
COQTHEORIES  := $(shell find src -type f -name "*.v")
JOBS         := 8

.PHONY: all clean

all: quick

dep: 
	./opam-pins.sh < opam.pins
	opam upgrade -y --jobs $(JOBS)
	opam pin add opam-builddep-temp "$$(pwd)#HEAD" -k git -n -y
	opam install opam-builddep-temp --deps-only -y --jobs $(JOBS)
	opam pin remove opam-builddep-temp

build: Makefile.coq
	mkdir -p .build
	rsync -avl --delete --exclude '*.vo' --exclude '*.vio' --exclude '*.v.d' --exclude '*.glob' --exclude '.*.aux' src Makefile.coq _CoqProject .build
	cd .build
	$(MAKE) -j -C .build -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src iRRAM"; \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -rf _CoqProject Makefile.coq .build
