#!/bin/sh
make all
make COQDOCFLAGS="--title 'HJ Formalization in Coq' -l --no-lib-name --toc-depth 0 " all.pdf
