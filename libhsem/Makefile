PROJ=hsem
BUILDDIR=$(PWD)/_build

OSTYPE:=$(shell ocamlfind ocamlc -config | awk '/^os_type:/ {print $$2}')
SYSTEM:=$(shell ocamlfind ocamlc -config | awk '/^system:/ {print $$2}')

ifeq ($(OSTYPE),$(filter $(OSTYPE),Win32 Cygwin))
OS = win
else ifeq ($(SYSTEM),$(filter $(SYSTEM),macosx))
OS = macos
else
OS = linux
endif

OCB = ocamlbuild

all: sharedlib build

sharedlib:
	$(OCB) lib$(PROJ).so -tag $(OS)
	cp $(BUILDDIR)/lib/lib$(PROJ).so $(BUILDDIR)/

build:
	$(OCB) -I src/ -I bin/ main.native
	cp $(BUILDDIR)/bin/main.native $(PROJ)

clean:
	$(OCB) -clean

test: all
	$(MAKE) -C $@
ifeq ($(OSTYPE),Win32)
	(cd test && PATH="$(BUILDDIR)/lib:$(PATH)" $(BUILDDIR)/test/test.native)
else
	(cd test && LD_LIBRARY_PATH=$(BUILDDIR)/lib $(BUILDDIR)/test/test.native)
endif

.PHONY: test build sharedlib
