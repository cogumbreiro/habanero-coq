#!/bin/sh
make all
make COQDOCFLAGS="--interpolate --title 'Habanero Formalization in Coq' -l --lib-subtitles " html
