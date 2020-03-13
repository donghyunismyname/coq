Print nat.
Print nat_rect.
Print nat_ind.
Print nat_rec.



Print bool.
Print bool_rect.
Check bool_rect.
Print bool_ind.
Check bool_ind.
Print bool_rec.

Check bool_rec.

Definition sewon :=
bool_rec (fun _ :bool => nat) O 1.

Definition sewon3 b :=
match b with
| true => 0
| false => 1
end.

Fixpoint dbl n :=
match n with
| 0 => 0
| S n => (dbl n) + 2
end.

Definition mydbl :=
nat_rec (fun _ => nat) O (fun _ m => m + 2).

Eval compute in (mydbl 10).


Print dbl.



Definition sewon2 :=
bool_rec (fun b : bool => if b then nat else bool) O true.

Eval compute in (sewon2 true).
Check sewon2.

Eval compute in (sewon true).
Eval compute in (sewon false).


Lemma sewon4 : bool -> nat.
Proof.
intro x.
destruct x.
exact O.
exact 1.
Defined.

Print bool.
Eval compute in (sewon true).
Eval compute in (sewon false).

Print sewon.

Lemma donghyun : nat -> bool.
Proof.
intro x.
destruct x.
exact true.
exact false.
Defined.

Eval compute in (donghyun 42).

Print donghyun.