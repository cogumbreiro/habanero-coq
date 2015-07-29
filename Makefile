.PHONY: coq clean gen-html gen-tex

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

gen-html:
	$(MAKE) -f Makefile.coq html COQDOCFLAGS="-interpolate -utf8 -g"

gen-tex:
	$(MAKE) -f Makefile.coq latex

clean:
	rm -f *.vo *.v.d *.glob
	rm -f */*.vo */*.v.d */*.glob */*~ */.#* Makefile.coq
	rm -f */*/*.vo */*/*.v.d */*/*.glob

%.tex: %.v
	coqdoc -l -latex $(head -n1 _CoqProject) $< -o $@

%.pdf: %.tex
	pdflatex $<
