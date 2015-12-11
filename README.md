# Habanero-Java Coq Formalization

Formalization of [HJ](https://wiki.rice.edu/confluence/display/HABANERO/Habanero-Java).

# Overview

```
├── Phasers
│   ├── PhaseOrdering.v: Defines ordering in a phasermap and over reduction
│   │
│   ├── Progress.v: Proves that DF has progress
│   │
│   ├── SubjectReduction.v: Proves that the DF-invariant is preserved by
│   │   redution
│   │
│   └── Welformedness.v: Defines welformedness; preserved by reduction
|
├── AsyncFinish
│   ├── Examples.v: Examples, including the definition of FX10
│   │
│   ├── Find.v: Shows that any task in a leaf finish cannot be blocked
│
├── All.v: Integrates the operations in AsyncFinish with Phasers for
    deadlock-freedom
```

DF: the deadlock-free language that only includes phasermap operations.
Redution: a binary relation over phasermaps (->) that represents execution of
an operation

DF-Invariant: the invariant required by DF to show progress, i.e.,
the transitive sum of displacements is a funtion.

Welformedness: defines that the signal phase should be >= than the wait phase,
and that if the task has wait-capability, then the difference between wait
and signal phase cannot be greater than 1.

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
