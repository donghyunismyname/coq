Require Import Setoid.

Definition prim_rec :=
  Eval compute in nat_rec (fun i : nat => nat).

Definition addition (a:nat) :=
  prim_rec a (fun _ n:nat => S n).

Eval compute in addition 10.


Lemma plus_n_O : forall n : nat, n = n + 0.
induction n.
reflexivity.
simpl.
rewrite IHn at 1.
reflexivity.
Qed.


Hint Resolve plus_n_O .

Lemma plus_n_S : forall n m:nat, S (n + m) = n + S m.
induction n.
simpl.
reflexivity.
simpl.
intro.
rewrite IHn.
reflexivity.
Qed.

Hint Resolve plus_n_S .

Lemma plus_com : forall n m:nat, n + m = m + n.
induction m.
simpl.
auto.
simpl.
rewrite <- IHm.
auto.
Qed.

Definition Is_S (n : nat) := 
match n with
| O => False
| S p => True
end.

Check Is_S.
Print Is_S.

Eval compute in Is_S 10.

Lemma S_Is_S : forall n:nat, Is_S (S n).
intro.
simpl.
trivial.
Qed.

Lemma no_confusion : forall n:nat, 0 <> S n.
red.
intros n H.
change (Is_S 0).
rewrite H.
simpl.
trivial.
Qed.



Inductive le (n : nat) : nat -> Prop :=
        | le_n : le n n
        | le_S : forall m : nat, le n m -> le n (S m).


Check le_n.
Check le_S.
Check le_ind.

Hint Constructors le.

Lemma le_n_S : forall n m : nat, le n m -> le (S n) (S m).
induction 1.
auto.
auto.
Qed.



Lemma tricky : forall n:nat, le n 0 -> n = 0.
intros.
inversion_clear H.
trivial.
Qed.

