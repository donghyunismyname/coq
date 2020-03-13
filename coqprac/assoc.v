Module ASS.

End ASS.

Check nat_rec.


Definition add :=
nat_rec
(fun _:nat => nat -> nat)
(fun x:nat => x)
(fun _:nat =>
 fun g:nat->nat =>
 fun n:nat =>
 S (g n)).



Definition C (n:nat) :=
forall b c:nat, (add (add n b) c) = (add n (add b c)).

Definition assoc_0:C 0 :=
fun b c:nat => eq_refl.

Definition lemlem: forall x y:nat, x=y -> S x = S y.
intros.
rewrite H.
reflexivity.
Qed.


Print lemlem.

Definition assoc_s: forall n:nat, C n -> C (S n) :=
fun n:nat =>
fun IH:C n =>
fun b c:nat => lemlem (add (add n b) c) (add n (add b c)) (IH b c).

Definition assoc:
forall n:nat, C n :=
nat_ind C assoc_0 assoc_s.
