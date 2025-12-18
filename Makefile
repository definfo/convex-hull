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

all: build

build:
> $(MAKE) -f CoqMakefile

clean:
> $(MAKE) -f CoqMakefile clean

.PHONY: all build clean
