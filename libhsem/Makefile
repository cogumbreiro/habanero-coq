PROJ=hsem
BUILDDIR=$(abspath _build)

ifeq ($(OS),Windows_NT)
  OSTYPE:=Win32
  DLL_EXT:=.dll
  EXE_EXT:=.exe
  NATIVE_EXT:=.exe
else
  NATIVE_EXT:=.native
  EXE_EXT:=
  OSTYPE:=$(shell uname -s)
  ifeq ($(OSTYPE),Linux)
    DLL_EXT:=.so
  endif
  ifeq ($(OSTYPE),Darwin)
    DLL_EXT:=.dylib
  endif
endif

PROJ_DLL = lib$(PROJ)$(DLL_EXT)

OCB = ocamlbuild
PROG = ./$(PROJ)$(EXE_EXT)
all: exe

dll:
	$(OCB) lib/$(PROJ_DLL) $(OCB_FLAGS)
	cp $(BUILDDIR)/lib/$(PROJ_DLL) $(BUILDDIR)/$(PROJ_DLL)

exe:
	$(OCB) main.native $(OCB_FLAGS)
	cp $(BUILDDIR)/bin/main$(NATIVE_EXT) $(PROG)

clean:
	$(OCB) -clean

test: dll
	$(MAKE) -C $@
	$(PROG) test/ok/*.jsonl
ifeq ($(OSTYPE),Win32)
	(cd test && PATH="$(BUILDDIR)/lib:$(PATH)" $(BUILDDIR)/test/test.native)
endif
ifeq ($(OSTYPE),Darwin)
	(cd test && DYLD_LIBRARY_PATH=${BUILDDIR}/lib $(BUILDDIR)/test/test.native)
endif
ifeq ($(OSTYPE),Linux)
	(cd test && LD_LIBRARY_PATH=${BUILDDIR}/lib $(BUILDDIR)/test/test.native)
endif

.PHONY: test dll exe
