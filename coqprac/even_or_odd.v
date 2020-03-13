Check nat_ind.
Check nat_rec.

About nat_ind.

Definition dbl:nat->nat 
:= nat_rec
(fun _:nat => nat)
0
(fun _:nat => fun n:nat => S (S n)).


Definition iseven:nat->Prop
:= fun n:nat => exists a, n = dbl a.

Definition isodd:nat->Prop
:= fun n:nat => exists a, n = S (dbl a).


Lemma haha: iseven 0 \/ isodd 0.
unfold iseven.
unfold isodd.
left.
exists 0.
reflexivity.
Qed.

Lemma hehe: 
forall n:nat, (iseven n) \/ (isodd n) -> (iseven (S n)) \/ (isodd (S n)).
unfold iseven.
unfold isodd.
intros.
destruct H.
destruct H.
right.
rewrite H.
exists x.
reflexivity.
left.
destruct H.
rewrite H.
exists (S x).
reflexivity.
Qed.




Lemma even_or_odd:
forall n:nat, (iseven n) \/ (isodd n).
unfold iseven.
unfold isodd.
induction n.
left.
exists 0.
reflexivity.
destruct IHn.
right.
destruct H.
rewrite H.
exists x.
reflexivity.
left.
destruct H.
rewrite H.
exists (S x).
reflexivity.
Qed.

Check even_or_odd.
Print even_or_odd.

Check nat_ind.

Definition proof :=
nat_ind
(fun n:nat => (iseven n) \/ (isodd n))
haha
hehe
.

Check proof.
