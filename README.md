# Coq Formalization of the Habanero programming model

Formalization of the
[Habanero programming model](https://wiki.rice.edu/confluence/display/HABANERO/Habanero-Java)
programming model.
We focus primarily on the formalization of [safety](https://en.wikipedia.org/wiki/Type_safety)
properties, such as deadlock freedom and race freedom.
The overarching goal of the project is to provide theoretical framework,
read a Coq library, for the verification of synchronization mechanisms.

# Publications

* Formalization of Habanero Phasers using Coq. Tiago Cogumbreiro, Jun Shirako, and Vivek Sarkar. JLAMP, 90:50–60, 2017. [*Download PDF.*](http://cogumbreiro.github.io/assets/cogumbreiro-formalizing-phasers.pdf) [*Online interpreter.*](https://cogumbreiro.github.io/jlamp17/)
* Formalization of phase ordering. Tiago Cogumbreiro, Jun Shirako, and Vivek Sarkar. In Proceedings of PLACES'16, 2016. [*Download PDF.*](https://github.com/cogumbreiro/habanero-coq/blob/places16/README.md)

# Overview

We are currently working on:

* deadlock-free subset of phaser operations
* async-finish 

# Using

Make sure you have [OPAM] installed.

To setup the requirements of this software do:
```
./configure.sh # to install dependencies and setup the environment
```

# Dependencies

* [OPAM] for the development.
* [Aniceto](https://bitbucket.org/cogumbreiro/aniceto-coq) (installed automatically)

[OPAM]: https://opam.ocaml.org/
