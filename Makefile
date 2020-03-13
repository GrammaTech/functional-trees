# Set personal or machine-local flags in a file named local.mk
ifneq ("$(wildcard local.mk)","")
include local.mk
endif

PACKAGE_NAME = functional-trees
PACKAGE_NICKNAME = ft

LISP_DEPS = $(wildcard *.lisp)

include .cl-make/cl.mk
