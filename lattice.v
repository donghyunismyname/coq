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


Definition partial_order {X:Set} (R:X->X->Prop) : Prop :=
  reflexive R /\ transitive R /\ antisymmetric R.

Definition partial_order_irrefl {X:Set} (R:X->X->Prop) :=
  irreflexive R /\ transitive R.


Definition erase_loop {X:Set} (R:X->X->Prop) : X->X->Prop :=
  fun (a b:X) => ~a=b /\ R a b.

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

      
     
    


