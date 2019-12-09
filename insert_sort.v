Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Omega.
Require Import Permutation.
Load sorted.

(* Auxiliar function: orderly insert a natural number in an ordered list *)
Fixpoint insert (x : nat) (xs : list nat) {struct xs} : list nat :=
match xs with
  | nil     => [x]
  | z :: zs =>
    match  x <=? z with       (* x <=? z = Nat.leb x z *)
      | true  => x :: (z :: zs)
      | false => z :: (insert x zs)
    end
end.

Fixpoint insert_sort (l : list nat) {struct l} : list nat :=
match l with
  | nil     => nil
  | x :: xs => insert x (insert_sort xs)
end.

Lemma insert_perm : forall (x : nat) (l : list nat), Permutation (insert x l) (x :: l).
Proof.
  induction l as [|x' l' IHl']; auto.
  simpl. destruct (x <=? x'); auto.
  apply perm_trans with (x' :: x :: l'); auto. apply perm_swap.
Qed.

Theorem permutation_insert_sort: forall l, Permutation l (insert_sort l).
Proof.
  induction l as [|x' l' IHl']; auto.
  assert (Permutation (x' :: l') (x' :: insert_sort l')); auto.
  simpl. rewrite H. rewrite insert_perm. reflexivity.
Qed.

Lemma insert_sorted_preserve : forall x l, Sorted l -> Sorted (insert x l).
Proof.
  intros x l H. induction H as [ | x' |x' x'' l' IHl' IHIHl']; simpl; auto.
  + remember (x <=? x') as bh. symmetry in Heqbh. destruct bh. 
  	- apply leb_complete in Heqbh. auto.
  	- apply leb_complete_conv in Heqbh. auto with *. 
	+ remember (x <=? x') as bh.  symmetry in Heqbh. destruct bh. 
		- apply leb_complete in Heqbh. auto.
		- remember (x <=? x'') as bh''. symmetry in Heqbh''. destruct bh''.
			* apply leb_complete in Heqbh''. apply leb_complete_conv in Heqbh. auto with *.
			* constructor; simpl in IHIHl'; rewrite Heqbh'' in IHIHl'; auto.
Qed.
Hint Resolve insert_sorted_preserve.

Theorem insert_sort_sorted : forall l, Sorted (insert_sort l).
Proof.
  intros. induction l as [|x' l']; simpl; auto.
Qed.

Theorem insert_sort_correct : Sorting_correct insert_sort.
Proof.
  constructor. split. apply insert_sort_sorted. apply permutation_insert_sort.
Qed.
