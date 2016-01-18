#!/bin/sh
make all
make COQDOCFLAGS="--interpolate --title 'HJ Formalization in Coq' -l --lib-subtitles " html
