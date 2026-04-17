SHELL := sh

CC ?= gcc
CFLAGS := -std=c99 -Wall -Wextra -Werror

SOURCE := main.c hull.c
TARGET := ./main

.PHONY: build clean

build:
	@$(CC) $(CFLAGS) $(SOURCE) -o $(TARGET)

clean:
	@rm -f $(TARGET)

