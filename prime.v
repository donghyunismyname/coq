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


