Require Import Coq.Arith.PeanoNat.

Axiom natext : forall f₁ f₂ : nat -> nat, (forall n, f₁ n = f₂ n) -> f₁ = f₂.



Definition baire := nat -> nat.


Fixpoint iseven (n : nat) : bool :=
  match n with
  | O => true
  | S m => if iseven m then false else true
  end.

Lemma natcomm : forall n m, n+m = m + n.
Proof.
  intros n m.
  induction n.
  auto.
  simpl.
  rewrite IHn.
  auto.
Defined.



Lemma evenodd : forall n, {k : nat & {k + k = n} + {k + k + 1 = n} }.
Proof.
  intro n.
  induction n.
  exists 0; left;  auto.

  destruct IHn.
  destruct s.
  exists x; right; rewrite e; rewrite natcomm; auto.

  exists (S x).
  left.
  simpl.
  auto.
  rewrite<- e.
  rewrite (natcomm (x+x) 1).
  simpl.
  rewrite <- natcomm.
  simpl.
  auto.
Defined.

Check (evenodd 10).

Definition concat : baire -> baire -> baire.
  intros α β.
  intro n.
  destruct (evenodd n).
  destruct s.
  exact (α x).
  exact (β x).
Defined.



Notation "⟨ β₁ , β₂ ⟩" := (concat β₁ β₂).


Definition π₁ : baire -> baire.
Proof.
  intro β.
  intro n.
  exact (β (n + n)).
Defined.

Definition π₂ : baire -> baire.
Proof.
  intro β.
  intro n.
  exact (β (n + n + 1)).
Defined.

Lemma dbl_inj : forall n m, n + n = m + m -> n = m.
Proof.
  intro n.
  induction n.
  intros.
  destruct m; auto.
  simpl in H; contradict H; auto.

  
  intro m.
  intro s.
  destruct m.

  simpl in s; contradict s; auto.
  assert (n+n=m+m).
  simpl in s.
  apply (eq_add_S (n+ S n) (m + S m)) in s.
  rewrite natcomm in s.
  simpl in s.
  assert (m + S m = S (m + m)).
  auto.
  rewrite H in s.
  auto.
  rewrite (IHn m H); auto.
Defined.

Lemma oddeven_contradict : forall m n, n+n+1 <> m + m.
Proof.

  intro m.
  induction m.
  intros.
  destruct n.
  simpl; auto.
  simpl; auto.

  intros.
  intro.
  induction n.

  simpl in H.
  
  assert (0 = m + S m) by auto.
  assert (m + S m = S (m + m)) as r by auto.
  rewrite r in H0.
   contradict H0;  auto.
  
  simpl in H.
  
  assert ((n + S n + 1) =  (m + S m)) by auto.
  Search (_ + (_ + _) = _ + _ + _).
  assert ( n + S n + 1 = (S n + n) + 1).
  rewrite (natcomm n (S n)); auto.
  rewrite (natcomm m (S m)) in H0.
  rewrite H1 in H0.
  simpl in H0.
  assert (n + n + 1 = m + m) by auto.
  exact (IHm n H2).
Defined.

Lemma evenodd_contradict : forall n m, n + n <> m + m + 1.
Proof.
  intros.
  intro p.
  assert (m+m+1=n+n) by auto.
  exact (oddeven_contradict n m H).
Defined.  



Lemma concat_safe : forall β₁ β₂, {γ & π₁ γ = β₁ /\  π₂ γ = β₂}.
Proof.
  intros β₁ β₂.
  exists (concat β₁ β₂).
  split.  
  apply natext.
  intro n.
  unfold π₁.
  unfold concat.
  
  
  induction (evenodd (n+n)).
  destruct p.

  rewrite  (dbl_inj x n e); auto.
  apply (oddeven_contradict) in e; contradict e.

  apply natext.
  intro n.
  unfold π₂.
  unfold concat.
  induction (evenodd (n + n + 1)).
  destruct p.

  apply (evenodd_contradict) in e; contradict e.
  

  (* rewrites *)
  assert (r1 : x + x + 1 = S (x + x)).
  rewrite natcomm; simpl; auto.
  assert (r2 : n + n + 1 = S (n + n)).
  rewrite natcomm; simpl; auto.
  rewrite r1 in e; rewrite r2 in e.
  assert (r : x + x = n + n); auto.
  rewrite  (dbl_inj x n r); auto.
Defined.

Lemma concat_proj_1 : forall β₁ β₂, β₁ = π₁ (concat β₁ β₂).
Proof.
  intros β₁ β₂.
  apply natext.
  intro n.
  unfold π₁.
  unfold concat.
  
  
  induction (evenodd (n+n)).
  destruct p.

  rewrite  (dbl_inj x n e); auto.
  apply (oddeven_contradict) in e; contradict e.
Defined.

Lemma concat_proj_2 : forall β₁ β₂, β₂ = π₂ (concat β₁ β₂).
Proof.
  intros β₁ β₂.
  apply natext.
  intro n.
  unfold π₂.
  unfold concat.
  
  
  induction (evenodd (n+n+1)).
  destruct p.
  apply (evenodd_contradict) in e; contradict e.
    assert (r1 : x + x + 1 = S (x + x)).
  rewrite natcomm; simpl; auto.
  assert (r2 : n + n + 1 = S (n + n)).
  rewrite natcomm; simpl; auto.
  rewrite r1 in e; rewrite r2 in e.
  assert (r : x + x = n + n); auto.
  rewrite  (dbl_inj x n r); auto.
Defined.


(**********)
(* partial functions and topology *)


Definition pfun := baire -> option baire.
Definition psubset := baire -> Prop.









Definition pdom (f : pfun) := fun β => exists β', f β = Some β' : Prop.

                                                           
                                
Definition continuous (f : pfun) := True.




(*
topology on baire space needs to be done...
 *)


(*
Definition pfun2 := {P : psubset & {β : baire | P β} -> baire}.


(* f₀ : 0::N → B f₀ β = 0ᴺ *)
Definition fzero : pfun2.
Proof.
  unfold pfun2.
  exists (fun β => β 0 = 0).
  intro x.
  destruct x.
  exact (fun _ => 0).
Defined.

Definition pdom2 (f : pfun2) := projT1 f.





Require Import List.
Definition prefix := list nat.

Inductive prefix2 : nat -> Set :=
  nil_prefix : prefix2 0
| succ_prefix : forall {n}, prefix2 n -> nat -> prefix2 (S n).

Print sigT.
Check projT2.

Inductive baire_mem : {n : nat & prefix2 n} -> baire -> Prop :=
  nil_mem : forall b, baire_mem (existT  (fun n => prefix2 n) 0  nil_prefix) b
| cons_mem : forall s b n, baire_mem s b -> (n = b (S (projT1 s))) ->
                           baire_mem
                             (existT (fun m => prefix2 m) (S (projT1 s)) (succ_prefix (projT2 s) n)) b.


Definition baseopen := {b : baire | exists p, baire_mem p b}.

Definition baireopen : Set

Definition intersect (a b : baseopen) : Set.
Proof.
  destruct a as [β t1].
  destruct b as [β₂ t2].
  exact {b : baire | exists 
                  

*)
