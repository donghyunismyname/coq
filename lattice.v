Definition reflexive {X:Set} (R:X->X->Prop) : Prop := 
  forall x:X, R x x.

Definition irreflexive {X:Set} (R:X->X->Prop) : Prop :=
  forall x:X, ~R x x.

Definition transitive {X:Set} (R:X->X->Prop) : Prop :=
  forall x y z:X, R x y -> R y z -> R x z.

Definition symmetric {X:Set} (R:X->X->Prop) : Prop :=
  forall x y:X, R x y -> R y x.

Definition antisymmetric {X:Set} (R:X->X->Prop) : Prop :=
  forall x y:X, R x y -> R y x -> x=y.


Definition add_loop {X:Set} (R:X->X->Prop) : X->X->Prop :=
  fun (a b:X) => a=b \/ R a b.



Theorem aaa {X:Set} : 
  forall R:X->X->Prop, partial_order R -> partial_order_irrefl (erase_loop R).
Proof.
  intro.
  unfold partial_order.
  unfold partial_order_irrefl.
  unfold erase_loop.
  split.
  - unfold irreflexive.
    intro. intro.
    destruct H0.
    apply H0. reflexivity.
  - unfold transitive.
    intros.
    destruct H0.
    destruct H1.
    destruct H.
    destruct H4.
    split.
    + intro. 
      enough (y=z). apply H1. exact H7.
      rewrite H6 in H2.
      unfold antisymmetric in H5.
      apply H5. exact H3. exact H2.
    + unfold transitive in H4.
      apply (H4 x y z). exact H2. exact H3.
Qed.


Theorem bbb {X:Set} :
  forall R:X->X->Prop, partial_order_irrefl R -> partial_order (add_loop R).
Proof.
  unfold partial_order.
  unfold partial_order_irrefl.
  intros.
  split.
  unfold reflexive. unfold add_loop.
  intros. left. reflexivity.
  split.
  unfold transitive. unfold add_loop. intros.
    inversion H0.
    inversion H1.
    left. rewrite H2. rewrite H3. reflexivity.
    right. rewrite H2. exact H3.
    inversion H1.
      right. rewrite <- H3. exact H2.
      right. inversion H. unfold transitive in H5. apply (H5 x y z).
      exact H2. exact H3.
  unfold antisymmetric. unfold add_loop.
  intros.
  inversion H0.
  exact H2.
  inversion H1.
  rewrite H3. reflexivity.
  unfold irreflexive in H.
  inversion H.
  enough False. inversion H6.
  apply (H4 x).
  unfold transitive in H5.
  apply (H5 x y x).
  exact H2. exact H3.
Qed.


Theorem ccc {X:Set} :
  forall R:X->X->Prop, reflexive R -> add_loop (erase_loop R) = R.
Proof.
  unfold add_loop. unfold reflexive. unfold erase_loop.
  intros. reflexivity.
