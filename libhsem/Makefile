PROJ=hsem
BUILDDIR=$(PWD)/_build
VPATH=$(BUILDDIR)
OCAMLDIR=$(shell ocamlopt -where)
$(shell mkdir -p $(BUILDDIR) $(BUILDDIR)/stub $(BUILDDIR)/lib $(BUILDDIR)/stub_generator $(BUILDDIR)/test $(BUILDDIR)/generated)
HSEM_PACKAGES=yojson
PACKAGES=$(HSEM_PACKAGES),ctypes.stubs,ctypes.foreign
BIN_PACKAGES=$(HSEM_PACKAGES),cmdliner

# The files used to build the stub generator.
GENERATOR_FILES=$(BUILDDIR)/lib/finish.cmx \
                $(BUILDDIR)/lib/hsem.cmx \
                $(BUILDDIR)/lib/bindings.cmx		\
                $(BUILDDIR)/stub_generator/generate.cmx

# The files from which we'll build a shared library.
LIBFILES=$(BUILDDIR)/lib/finish.cmx \
         $(BUILDDIR)/lib/hsem.cmx			\
         $(BUILDDIR)/lib/bindings.cmx			\
         $(BUILDDIR)/generated/$(PROJ)_bindings.cmx	\
         $(BUILDDIR)/lib/apply_bindings.cmx		\
         $(BUILDDIR)/generated/$(PROJ).o

CAML_INIT=$(BUILDDIR)/stub/init.o

# The files that we'll generate
GENERATED=$(BUILDDIR)/generated/$(PROJ).h \
          $(BUILDDIR)/generated/$(PROJ).c \
          $(BUILDDIR)/generated/$(PROJ)_bindings.ml

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
	$(OCB) -I lib/ -I bin/ main.native

stubs: $(GENERATED)

$(BUILDDIR)/stub/%.o:
	ocamlc -g -c stub/init.c
	mv init.o $@

$(GENERATED): $(GENERATOR)
	$(GENERATOR) $(BUILDDIR)/generated

$(BUILDDIR)/%.o: %.c
	$(CC) -c -o $@ -fPIC -I $(shell ocamlfind query ctypes) -I $(OCAMLDIR) -I $(OCAMLDIR)/../ctypes $<

$(BUILDDIR)/%.cmi: %.mli
	ocamlfind ocamlc -o $@ -c $<

$(BUILDDIR)/%.cmx: %.ml $(BUILDDIR)/lib/finish.cmi
	ocamlfind opt -c -o $@ -I $(BUILDDIR)/generated -I $(BUILDDIR)/lib -package $(PACKAGES) $<

$(BUILDDIR)/%.cma: %.ml $(BUILDDIR)/lib/finish.cmi  
	ocamlfind opt -c -o $@ -I $(BUILDDIR)/generated -I $(BUILDDIR)/lib -package $(PACKAGES) $<

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
