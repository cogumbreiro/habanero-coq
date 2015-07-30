# Habanero-Java Coq Formalization

Formalization of [HJ](https://wiki.rice.edu/confluence/display/HABANERO/Habanero-Java).

# Development

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
