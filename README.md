# Coq Formalization of Habanero-Java

Formalization of the
[Habanero-Java](https://wiki.rice.edu/confluence/display/HABANERO/Habanero-Java)
programming model.
We focus primarily on the formalization of [safety](https://en.wikipedia.org/wiki/Type_safety)
properties, such as deadlock freedom and race freedom.
The overarching goal of the project is to provide theoretical framework,
read a Coq library, for the verification of synchronization mechanisms.

# Overview

We are currently working on:
* [PLACES'16 project page](https://github.com/cogumbreiro/hj-coq/wiki/PLACES%2716): Formalization of Phase Ordering
* deadlock-free subset of phaser operations
* async-finish 

# Using HJ-Coq

We use [OPAM](https://opam.ocaml.org/) and [Coq Shell](https://github.com/coq/opam-coq-shell)
for the development.

This project depends on [Aniceto](https://bitbucket.org/cogumbreiro/aniceto-coq),
so you need to install it first:
```
git clone https://bitbucket.org/cogumbreiro/aniceto-coq
```

To setup the requirements of this software do:
```
source dev.sh # to install dependencies and setup the environment
```

# Setting up CoqIDE in MacOS X

To setup CoqIDE in MacOS you need to set the path of `coqtop` to be aware
of your OPAM installation.

Navigate to `CoqIDE -> Externals -> coqtop` and set the output of the
following command:

```
which coqtop
```
