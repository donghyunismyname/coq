Lemma nonzero_iff_exists_predecessor: 
forall a:nat, a <> 0 <-> (exists p:nat, a = S p).
split.
intros.
destruct a.
tauto.
exists a.
reflexivity.
intros.
destruct H.
rewrite H.
discriminate.
Qed.





Fixpoint add (a b:nat) :=
match b with
| 0 => a
| S n => S (add a n)
end.
Notation "a + b" := (add a b).



Lemma addassoc: forall a b c:nat, 
(add a (add b c)) = (add (add a b) c).
intros.
elim c.
simpl.
trivial.
intro n.
intro H.
simpl.
rewrite H.
trivial.
Qed.


Lemma addcomm1: forall a b:nat,
add (S a) b = add a (S b).
intros.
elim b.
simpl.
trivial.
intros.
simpl.
rewrite H.
simpl.
trivial.
Qed.

Lemma addcomm: forall a b:nat, 
(add a b) = (add b a).
intros.
elim a.
elim b.
trivial.
intros.
simpl.
rewrite H.
simpl.
trivial.
intros.
simpl.
rewrite  <- H.
apply addcomm1.
Qed.

Fixpoint mul a b:nat :=
match b with
| 0 => 0
| S n => add (mul a n) a
end.

Lemma distL: forall k a b:nat,
mul k (add a b) = add (mul k a) (mul k b).
intros.
elim b.
simpl.
trivial.
intros.
simpl.
rewrite addassoc.
rewrite H.
trivial.
Qed.

Lemma distR: forall k a b:nat,
mul (add a b) k = add (mul a k) (mul b k).
intros.
elim k.
simpl.
trivial.
intros.
simpl.
enough (
forall an a1 bn b1:nat,
add (add an bn) (add a1 b1)
=
add (add an a1) (add bn b1)
).
rewrite H0.
rewrite H.
trivial.
intros.
rewrite addassoc.
rewrite addassoc.
replace (add (add an bn) a1)
with (add (add an a1) bn).
trivial.
rewrite <- addassoc.
rewrite <- addassoc.
enough (add a1 bn = add bn a1).
rewrite H0.
trivial.
apply addcomm.
Qed.


Lemma mulassoc: forall a b c:nat,
(mul a (mul b c)) = (mul (mul a b) c).
intros.
elim c.
simpl.
trivial.
intros.
simpl.
rewrite distL.
rewrite H.
trivial.
Qed.

Lemma multiplication_by_zero_is_zero: forall a:nat,
mul 0 a = 0.
intros.
elim a.
trivial.
intros.
simpl.
exact H.
Qed.

Lemma mulcomm: forall a b:nat,
mul a b = mul b a.
intros.
elim b.
simpl.
elim a.
trivial.
intros.
simpl.
exact H.
intros.
replace (S n)
with (add n 1).
rewrite distL.
rewrite distR.
rewrite H.
replace (mul a 1)
with (mul 1 a).
trivial.
elim a.
simpl.
trivial.
intros.
simpl.
rewrite H0.
simpl.
trivial.
simpl.
trivial.
Qed.



Lemma nonzero_times_nonzero_is_nonzero:
forall a b:nat, a<>0 /\ b<>0 -> mul a b <> 0.
intros.
destruct H.
apply nonzero_iff_exists_predecessor in H.
apply nonzero_iff_exists_predecessor in H0.
destruct H.
destruct H0.
rewrite H.
rewrite H0.
simpl.
discriminate.
Qed.


Lemma product_zero_implies_multiplicands_zero: 
forall a b:nat, mul a b = 0 -> a = 0 \/ b = 0.
destruct a.
tauto.
destruct b.
tauto.
simpl.
discriminate.
Qed.



Lemma product_nonzero_implies_multiplicands_nonzero:
forall a b:nat, mul a b <> 0 -> a<>0 /\ b<>0.
destruct a.
intro.
rewrite multiplication_by_zero_is_zero.
tauto.
destruct b.
simpl.
tauto.
intro.
split.
discriminate.
discriminate.
Qed.


Fixpoint eq (a b:nat) :=
match a with
| 0 => 
  match b with 
  | 0 => true
  | S pb => false
  end
| S pa =>
  match b with
  | 0 => false
  | S pb => (eq pa pb)
  end
end.

Fixpoint leq (a b:nat) :=
match a with
| 0 => true
| S pa =>
  match b with
  | 0 => false
  | S pb => (leq pa pb)
  end
end.


Fixpoint rem (a m:nat) :=
match a with
| 0 => 0
| S n => 
  let r := rem n m in
  if (eq (S r) m) then 0 else (S r)
end.


Lemma rem_is_zero_iff_exists_divisor:
forall a m:nat, m<>0 -> ((rem a m) = 0 <-> exists d:nat, (mul m d) = a).
induction a.
simpl.
split.
intros.
exists 0.
simpl.
reflexivity.
tauto.
intros.
simpl.


Definition div (a b:nat) :=
exists d:nat, (mul a d) = b.

Definition leq (a b:nat) :=
exists aa:nat, (add a aa) = b.

Definition less (a b:nat) :=
exists aa:nat, (add a (S aa)) = b.





Lemma div_implies_leq:
  forall a b:nat, b<>0 /\ (div a b) -> (leq a b).
unfold div.
unfold leq.
intros.
destruct H.
destruct H0.
assert (x <> 0).
intro.
rewrite H1 in H0.
rewrite <- H0 in H.
generalize H.
simpl.
tauto.
assert (exists px:nat, x = S px).
apply nonzero_has_predecessor.
assumption.
destruct H2.
exists (mul a x0).
enough (add (mul a 1) (mul a x0) = b).
generalize H3.
simpl.
replace (add 0 a) with a.
tauto.
rewrite addcomm.
simpl.
reflexivity.
rewrite <- distL.
rewrite addcomm.
rewrite <- H0.
replace (add x0 1) with x.
reflexivity.
Qed.




Definition prime (p:nat) :=
(leq 2 p) /\ ~ exists d:nat, d<>1 /\ d<>p /\ (div d p).

Lemma asaf: prime 7.
unfold prime.
split.
unfold leq.
exists 5.
reflexivity.
unfold div.
intro.
destruct H.
destruct H.
destruct H0.
destruct H1.
induction x0.
discriminate.
apply IHx0.




Lemma primes_are_infinite:
forall n:nat, exists p:nat, (leq n p) /\ (prime p).
unfold prime.
unfold leq.
unfold div.









