# Formalization of Phase Ordering

## Abstract

Phasers pose an interesting synchronization mechanism that generalizes many collective
synchronization patterns seen in parallel programming languages, including barriers, clocks, and
point-to-point synchronization using latches or semaphores. This work characterizes scheduling constraints
on phaser operations, by relating the execution state of two tasks that operate on the same phaser.
We propose a formalization of Habanero phasers, May-Happen-In-Parallel, and Happens-Before
relations for phaser operations, and show that these relations conform with the semantics. Our
formalization and proofs are fully mechanized using the Coq proof assistant, and are available online.


# Resources

* [Paper pre-print](https://github.com/cogumbreiro/habanero-coq/raw/places16/preprint.pdf)
* [Browse documentation](http://cogumbreiro.github.io/places16/coqdoc/toc.html)
* [Download source-code (zip)](https://github.com/cogumbreiro/hj-coq/archive/places16.zip)
* [Browse source-tree](https://github.com/cogumbreiro/hj-coq/tree/places16)
