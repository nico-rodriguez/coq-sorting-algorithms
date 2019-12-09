Require Import List.
Import ListNotations.
Require Import Permutation.

Inductive Sorted : list nat -> Prop :=
	| sorted_nil	: Sorted []
	| sorted_sing : forall e, Sorted [e]
	| sorted_cons	: forall e h t, Sorted (h :: t) -> e <= h -> Sorted (e :: h :: t).

Hint Constructors Sorted.

Inductive Sorting_correct (algo : list nat -> list nat) :=
	| sorting_spec_intro :
    (forall l, Sorted (algo l) /\ Permutation l (algo l)) -> Sorting_correct algo.
