#!/bin/sh
coq_makefile -f _CoqProject -o convexhull-coq.mk
make -B -f convexhull-coq.mk
