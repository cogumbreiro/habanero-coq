# hsem: Habanero Semantics Checker for C

The Habanero semantics checker for C is a C library used to check existing
Habanero implementations. The library can be used in one of two ways:

* **Offline verification:** `hsem` verifies if a given an execution trace file
   is valid.

* **Interactive verification:** `hsem` maintains a verification state to which
  the user adds observed operations to be checked.

Currently we only support `async-finish` like operations, which means that
we are able to verify: hclib async/finish and Cilk spawn/sync.

# Setup

Run the following script **once** to download the compile-time dependencies:
```
./configure.sh
```

To compile this project just run `make`:
```
make
```
This command will generate the two following files:
```
_build/generated/hsem.h
_build/libhsem.so
```

# Examples

Check out file [test.c](test/test.c) for examples.

