# - The -I flag introduces sub-directories 
# - -use-ocamlfind is required to find packages (from Opam)
# - _tags file introduces packages, bin_annot flag for tool chain

OCB_FLAGS = -use-ocamlfind -I . -plugin-tag "package(js_of_ocaml.ocamlbuild)"
OCB = 		ocamlbuild $(OCB_FLAGS)

all: 		byte js # profile debug

clean:
			$(OCB) -clean

#native: 	sanity
#			$(OCB) main.native

byte:		sanity
			$(OCB) main.byte

js:		sanity
			$(OCB) main.js

profile: 	sanity
			$(OCB) -tag profile main.native

debug: 		sanity
			$(OCB) -tag debug main.byte

sanity:
			# check that packages can be found
			ocamlfind query yojson 

test: 		native
			echo '[1, 2, "three", {"four": 4}]' | ./main.native 

.PHONY: 	all clean byte native profile debug sanity test
