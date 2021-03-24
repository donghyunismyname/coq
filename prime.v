Fixpoint eqb (a b:nat):bool :=
  match a, b with
  | 0, 0 => true
  | S aa, S bb => eqb aa bb
  | _, _ => false
  end.

Notation "a =? b" := (eqb a b) (at level 10).

Lemma eqb_eq: forall a b:nat, a =? b = true <-> a = b.
Proof.
  induction a.
  - destruct b.
    + split. auto. auto.
    + split. intro. inversion H. intro. inversion H.
  - destruct b.
    + split. intro. inversion H. intro. inversion H.
    + simpl. split.
      * intro.
        enough (a=b). rewrite H0. reflexivity.
        apply IHa. apply H.
      * intro.
        apply IHa.
        inversion H.
        reflexivity.
Qed.


Lemma neqb_neq: forall a b:nat, a=?b = false <-> a<>b .
split.
intros. intro. rewrite H0 in H.
enough (forall n:nat, n=?n = true).
rewrite H1 in H. discriminate.
induction n. reflexivity. simpl. apply IHn.
generalize a as x. generalize b as y.
induction y, x.
- intros. assert (0=0). reflexivity. contradiction.
- intros. simpl. reflexivity.
- intros. simpl. reflexivity.
- intro. simpl. apply IHy. intro. assert (S x = S y).
rewrite H0. reflexivity. apply H. apply H1.
Qed.


Fixpoint leb (a b:nat):bool :=
  match a, b with
  | 0, _ => true
  | S aa, 0 => false
  | S aa, S bb => leb aa bb
  end.

Notation "a <=? b" := (leb a b) (at level 10).

Lemma le_0_Sn: forall n:nat, 0 <= S n.
Proof.
induction n.
  - apply le_S. apply le_n.
  - apply le_S. apply IHn.
Qed.

Lemma le_Sa_Sb: forall a b:nat, a<=b <-> S a <= S b.
Proof.
intro a. induction b.
- split.
  + intro. inversion H. apply le_n.
  + intro. inversion H.
    * apply le_n.
    * inversion H1.
- split.
  + intro. inversion H.
    * apply le_n.
    * apply le_S. apply IHb. apply H1.
  + intro. inversion H.
    * apply le_n.
    * apply le_S. apply IHb. apply H1.
Qed.


Lemma leb_le : forall a b:nat, a <=? b = true <-> a <= b.
Proof.
  induction a, b.
  - split. auto. auto.
  - split.
    + intro. induction b. auto. 
      apply le_S. apply IHb. apply H.
    + intros. reflexivity.
  - split.
    + intros. inversion H.
    + intro. inversion H.
  - split.
    + intro. apply -> le_Sa_Sb.
      inversion H. apply IHa. apply H1.
    + intro. apply <- le_Sa_Sb in H.
      apply IHa in H. simpl. apply H.
Qed.


Lemma neq_lt : forall a b:nat, a<>b <-> a<b \/ b<a.
induction a, b.
- split. 
  + intro. contradiction.
  + intro. destruct H. inversion H. inversion H.
- split.
  + intro. left. apply leb_le. simpl. reflexivity.
  + intro. intro. apply eqb_eq in H0. simpl in H0. discriminate.
- split.
  + intro. right. apply -> le_Sa_Sb. apply leb_le. reflexivity.
  + intro. intro. apply eqb_eq in H0. simpl in H0. discriminate.
- split.
  + intro. assert (a <> b).
    enough (forall A B:Prop, (A<->B) -> ~A -> ~B).
    apply (H0 (S a = S b) (a=b)).
    split. intro. inversion H1. reflexivity.
    intro. rewrite H1. reflexivity.
    apply H.
    intros. intro. apply H1. apply H0. apply H2.
    apply IHa in H0. destruct H0.
    left. apply le_Sa_Sb in H0. apply H0.
    right. apply le_Sa_Sb in H0. apply H0.
  + intros. destruct H.
    * unfold "<" in H. apply le_Sa_Sb in H. unfold "<" in IHa.
      assert (S a <= b \/ S b <= a). left. apply H.
      apply IHa in H0.
      enough (forall A B:Prop, A<->B -> ~A -> ~B).
      apply (H1 (a=b)). split. intro. rewrite H2. reflexivity.
      intro. inversion H2. reflexivity. apply H0.
      intros. intro. apply H2. apply H1. apply H3.
    * unfold "<" in H.
      unfold "<" in IHa.
      assert (a<>b -> S a <> S b).
      intro. intro. apply H0. inversion H1. reflexivity.
      apply H0. apply IHa. right.
      apply le_Sa_Sb. apply H.
Qed.



Inductive natlist :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
Notation "x :: xs" := (cons x xs).

Fixpoint length (xs:natlist): nat :=
match xs with
| [] => 0
| _::ys => S (length ys)
end.

Fixpoint contain (xs:natlist)(x:nat) : bool :=
match xs with
| [] => false
| y::ys => if x=?y then true else contain ys x
end.

Print option.

Fixpoint access (xs:natlist)(i:nat) : option nat :=
match xs, i with
| [], _ => None
| y::ys, 0 => Some y
| y::ys, S j => access ys j
end.


Fixpoint sort_insert (x:nat)(xs:natlist):natlist :=
match xs with
| [] => [x]
| y::ys => if x<=?y then x::y::ys else y::(sort_insert x ys)
end.
Fixpoint sort (xs:natlist):natlist :=
match xs with
| [] => []
| y::ys => sort_insert y (sort ys)
end.






Goal forall a b:nat, a<>b -> exists x:nat, 1 <=x /\ (x=a \/ x=b).
intros. apply neq_lt in H. destruct H.
- exists b. split. unfold "<" in H.
  induction a. apply H. apply IHa.
  enough (forall x y z:nat, x<=y -> y<=z -> x<=z).
  apply (H0 (S a) (S (S a))).
  apply le_S. apply le_n. apply H.
  in
  






Definition composite (n:nat) := exists a b:nat, 1<a /\ 1<b /\ n=a*b.
Definition prime (n:nat) := ~ composite n.



Fixpoint factorize (n:nat) : natlist.
Admitted.

Theorem factorize_is_distinct :
forall n:nat, 




Theorem arbitrarily_large_prime: forall n:nat, exists p:nat, n <= p /\
  ~ exists a b:nat, 1<a /\ 1<b /\ p=a*b.
Proof.
Admitted.


