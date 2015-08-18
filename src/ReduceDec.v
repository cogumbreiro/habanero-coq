
Require Import HJ.Lang.
Require Import HJ.Typesystem.
Require Import HJ.Vars.

Lemma check_dec:
  forall t i pm,
  { Check t i pm } + { ~ Check t i pm }.
Admitted.

Theorem reduce_dec:
  forall t i pm,
  { exists pm', Reduce pm t i pm' } + { forall pm', ~ Reduce pm t i pm' }.
Proof.
  intros.
  destruct (check_dec t i pm).
  - left.
    