SHELL := bash
.ONESHELL:
.SHELLFLAGS := -eu -o pipefail -c
.DELETE_ON_ERROR:
# MAKEFLAGS += --warn-undefined-variables
MAKEFLAGS += --no-builtin-rules

# Replace <TAB> usage with block character `>`
ifeq ($(origin .RECIPEPREFIX), undefined)
	$(error This Make does not support .RECIPEPREFIX. Please use GNU Make 4.0 or later)
endif
.RECIPEPREFIX = >

all: generate build

generate:
> coq_makefile -f _CoqProject -o CoqMakefile

build: generate
> $(MAKE) -f CoqMakefile

clean: generate
> $(MAKE) -f CoqMakefile clean

clean-dist:
> rm -f CoqMakefile CoqMakefile.conf .Makefile.coq.d
> find . -type f -name '*.(vo|vok|vos|glob|aux)' -delete

.PHONY: all generate build clean clean-dist
