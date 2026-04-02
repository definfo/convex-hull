SHELL := sh

CC ?= gcc
CFLAGS := -std=c99 -Wall -Wextra -Werror

SOURCE := uva681_graham_scan.c
TARGET := ./graham_scan

.PHONY: build test clean

build:
	@$(CC) $(CFLAGS) $(SOURCE) -o $(TARGET)

test: build
	@$(TARGET) < testcases/1.in > testcases/1.out.tmp
	@diff testcases/1.out.tmp testcases/1.out && printf "Passed ✅\n"

clean:
	@rm -f $(TARGET) testcases/*.out.tmp

