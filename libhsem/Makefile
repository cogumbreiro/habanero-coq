PROJ=hsem
BUILDDIR=$(PWD)/_build
VPATH=$(BUILDDIR)
OCAMLDIR=$(shell ocamlopt -where)
$(shell mkdir -p $(BUILDDIR) $(BUILDDIR)/src $(BUILDDIR)/lib $(BUILDDIR)/support $(BUILDDIR)/test $(BUILDDIR)/generated)
HSEM_PACKAGES=yojson
PACKAGES=$(HSEM_PACKAGES),ctypes.stubs,ctypes.foreign
BIN_PACKAGES=$(HSEM_PACKAGES),cmdliner

# The files used to build the stub generator.
GENERATOR_FILES=$(BUILDDIR)/src/finish.cmx \
                $(BUILDDIR)/src/hsem.cmx \
                $(BUILDDIR)/lib/bindings.cmx		\
                $(BUILDDIR)/support/generate.cmx

# The files from which we'll build a shared library.
LIBFILES=$(BUILDDIR)/src/finish.cmx \
         $(BUILDDIR)/src/hsem.cmx			\
         $(BUILDDIR)/lib/bindings.cmx			\
         $(BUILDDIR)/generated/$(PROJ)_bindings.cmx	\
         $(BUILDDIR)/lib/apply_bindings.cmx		\
         $(BUILDDIR)/generated/$(PROJ)_stubs.o

CAML_INIT=$(BUILDDIR)/support/init.o

# The files that we'll generate
GENERATED=$(BUILDDIR)/generated/$(PROJ).h \
          $(BUILDDIR)/generated/$(PROJ)_stubs.c \
          $(BUILDDIR)/generated/$(PROJ)_bindings.ml
INCS=-I $(BUILDDIR)/generated -I $(BUILDDIR)/lib -I $(BUILDDIR)/src  -package $(PACKAGES)
OSTYPE:=$(shell ocamlfind ocamlc -config | awk '/^os_type:/ {print $$2}')
SYSTEM:=$(shell ocamlfind ocamlc -config | awk '/^system:/ {print $$2}')
EXTDLL:=$(shell ocamlfind ocamlc -config | awk '/^ext_dll:/ {print $$2}')
CC:= $(shell ocamlfind ocamlc -config | awk '/^bytecomp_c_compiler/ {for(i=2;i<=NF;i++) printf "%s " ,$$i}')

ifeq ($(OSTYPE),$(filter $(OSTYPE),Win32 Cygwin))
EXTEXE=.exe
else
EXTEXE=
endif

GENERATOR=$(BUILDDIR)/generate$(EXTEXE)

OCB = ocamlbuild

all: sharedlib build

sharedlib: $(BUILDDIR)/lib$(PROJ)$(EXTDLL)

ifeq ($(OSTYPE),$(filter $(OSTYPE),Win32 Cygwin))
$(BUILDDIR)/lib$(PROJ)$(EXTDLL): $(CAML_INIT) $(LIBFILES)
	ocamlfind opt -o $@ -linkpkg -output-obj -verbose -package $(PACKAGES) $^
else ifeq ($(SYSTEM),$(filter $(SYSTEM),macosx))
$(BUILDDIR)/lib$(PROJ)$(EXTDLL): $(CAML_INIT) $(LIBFILES)
	ocamlfind opt -o $@ -linkpkg -runtime-variant _pic -verbose -ccopt -dynamiclib -package $(PACKAGES) $^
else
$(BUILDDIR)/lib$(PROJ)$(EXTDLL): $(CAML_INIT) $(LIBFILES)
	ocamlfind opt -o $@ -linkpkg -output-obj -runtime-variant _pic -verbose -package $(PACKAGES) $^
endif

build:
	$(OCB) -I src/ -I bin/ main.native
	cp $(BUILDDIR)/bin/main.native $(PROJ)

stubs: $(GENERATED)

$(BUILDDIR)/support/%.o:
	ocamlc -g -c support/init.c
	mv init.o $@

$(GENERATED): $(GENERATOR)
	$(GENERATOR) $(BUILDDIR)/generated

$(BUILDDIR)/%.o: %.c
	$(CC) -c -o $@ -fPIC -I $(shell ocamlfind query ctypes) -I $(OCAMLDIR) -I $(OCAMLDIR)/../ctypes $<

$(BUILDDIR)/%.cmi: %.mli
	ocamlfind ocamlc -o $@ -c $<

$(BUILDDIR)/%.cmx: %.ml $(BUILDDIR)/src/finish.cmi
	ocamlfind opt -c -o $@ $(INCS) $<

$(BUILDDIR)/%.cma: %.ml $(BUILDDIR)/src/finish.cmi  
	ocamlfind opt -c -o $@ $(INCS) $<

$(GENERATOR): $(GENERATOR_FILES)
	ocamlfind opt -o $@ -linkpkg -package $(PACKAGES) $^

clean:
	rm -rf $(BUILDDIR)

test: all
	$(MAKE) -C $@
ifeq ($(OSTYPE),Win32)
	(cd test && PATH="$(BUILDDIR):$(PATH)" $(BUILDDIR)/test/test.native)
else
	(cd test && LD_LIBRARY_PATH=$(BUILDDIR) $(BUILDDIR)/test/test.native)
endif

.PHONY: test build
