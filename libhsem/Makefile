PROJ=hsem
BUILDDIR=$(PWD)/_build

ifeq ($(OS),Windows_NT)
  OSTYPE:=Win32
  DLL_EXT:=.dll
else
  OSTYPE:=$(shell uname -s)
  ifeq ($(OSTYPE),Linux)
    DLL_EXT:=.so
  endif
  ifeq ($(OSTYPE),Darwin)
    DLL_EXT:=.dylib
  endif
endif

OCB = ocamlbuild

all: build

sharedlib:
	$(OCB) lib$(PROJ).so $(OCB_FLAGS)
	cp $(BUILDDIR)/lib/lib$(PROJ)$(DLL_EXT) $(BUILDDIR)/

build:
	$(OCB) -I src/ -I bin/ main.native $(OCB_FLAGS)
	cp $(BUILDDIR)/bin/main.native $(PROJ)

clean:
	$(OCB) -clean

test: sharedlib
	$(MAKE) -C $@
ifeq ($(OSTYPE),Win32)
	(cd test && PATH="$(BUILDDIR)/lib:$(PATH)" $(BUILDDIR)/test/test.native)
else
	(cd test && LD_LIBRARY_PATH="$(BUILDDIR)"/lib $(BUILDDIR)/test/test.native)
endif

.PHONY: test build sharedlib
