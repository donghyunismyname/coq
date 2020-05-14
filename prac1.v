

Goal forall x y:nat, x=y \/ x<>y.
Proof.
  induction x.
  - induction y.
    + left. reflexivity.
    + right. discriminate.
  - induction y.
    + right. discriminate.
    + destruct (IHx y).
      * left. rewrite H. reflexivity.
      * right. intro. inversion H0. apply H. exact H2.
Qed.







Definition eq_symm: forall {T:Type}, forall {a b:T}, a=b -> b=a :=
  fun (T:Type)(a b:T)(H:a=b) =>
    eq_ind a 
      (fun x:T => x = a)
      eq_refl
      b H.


Definition S_function: forall a b:nat, a=b -> S a = S b :=
fun (a b:nat)(E:a=b) => 
  eq_ind a (fun y:nat => S a = S y)
         eq_refl b E.

Definition eqb :=
  let eq0b : nat->bool := 
    nat_rec (fun _:nat=>bool) true (fun (_:nat)(_:bool) => false) in
  nat_rec (fun _:nat => nat->bool)
    eq0b
    (fun (_:nat)(eqnb:nat->bool) => 
      nat_rec (fun _:nat=>bool) 
        false
        (fun (a:nat)(_:bool) => eqnb a)).





Definition pred : nat -> nat :=
  nat_rec (fun _:nat => nat) 
    0 
    (fun (n:nat)(_:nat) => n).

Definition id_pred_S : forall n:nat, n = pred (S n) :=
  fun n:nat => eq_refl.

Theorem S_injective_t: forall a b:nat, S a = S b -> a = b.
Proof.
  intros.
  rewrite (id_pred_S a).
  rewrite (id_pred_S b).
  rewrite H.
  reflexivity.
Qed.

Print S_injective_t.


Definition S_injective : forall a b:nat, S a = S b -> a = b := 
  fun (a b:nat)(H:S a = S b) =>
    let h1 : pred (S a) = pred (S b) := 
      eq_ind (S a) (fun x:nat => pred (S a) = pred x) eq_refl (S b) H in
    let h2 : pred (S a) = b := 
      eq_ind (pred (S b)) (fun x:nat => pred (S a) = x) h1 b eq_refl in
    let h3 : a = b := 
      eq_ind (pred (S a)) (fun x:nat => x = b) h2 a eq_refl in
    h3.














Definition notb : bool->bool :=
  bool_rec (fun _:bool=>bool) false true.


Definition double : nat->nat :=
  nat_rec (fun _:nat=>nat) 0 (fun (_:nat)(u:nat) => S (S u)).

Definition evenb : nat->bool :=
  nat_rec (fun _:nat=>bool) true (fun (_:nat)(u:bool) => notb u).

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n:nat, even n -> even (S (S n)).


Lemma lem01 : forall n:nat, exists k:nat, n = double k \/ n = S (double k).
  induction n.
  - exists 0. left. reflexivity.
  - destruct IHn. destruct H.
    + 




Theorem aaaa : forall n:nat, evenb n = true <-> exists k:nat, n = double k.
Proof.
  induction n.
  - simpl. split.
    + intros. exists 0. reflexivity.
    + intros. reflexivity.
  - simpl. split.
    + 





Theorem ev_inversion :
  forall(n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : even 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : even (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.




Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
intros.
destruct H.
inversion H.
  



Fixpoint evenb (n:nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S x) => evenb x
  end.



Check ex_intro.

Lemma double_or_S_double : forall n, exists k, n = double k \/ n = S (double k).
  induction n.
  - exists 0. simpl. left. reflexivity.
  - destruct IHn. destruct H.
    + exists x. right. rewrite H. reflexivity.
    + exists (S x). left. rewrite H. simpl. reflexivity.
Qed.

Print double_or_S_double.

Lemma evenb_double : forall n, evenb n = true <-> exists k, n = double k.
Proof.
  intro n.
  inversion (double_or_S_double n).  

  destruct n.
  - simpl. split.
    + intro. exists 0. simpl. reflexivity.
    + intro. reflexivity.
  - destruct double_or_S_double.


Lemma evenb_true_or_false : forall n, evenb n = true \/ evenb n = false.
Proof.
  induction n.
  - simpl. left. reflexivity.
  - inversion IHn.
    + right. 







Lemma even_evenb : forall n, even n <-> evenb n = true.
Proof.
  induction n.
  - simpl. split.
    + reflexivity.
    + intro. apply ev_0.
  - split.






Inductive day : Type :=
| mon
| tue
| wed.
Check mon.
Check day.
Check day.


Inductive lele : nat -> Prop :=
| aaa : lele
| bbb : lele.



Definition nextday (d:day) :day :=
  match d with
  | mon => tue
  | tue => wed
  | wed =>  mon
  end.

Definition foo (a:day) (b:day) : day :=
  match a with
  | mon => match b with
           | mon => mon
           | tue => tue
           | wed => wed
           end
  |tue => tue
  | wed => wed
  end.


Fixpoint factorial (n:nat) :=
  match n with
  | O => 1
  | S a => n * (factorial a)
  end.





















  
Section Predicate_calculus.





Print and_ind.


Definition haha:
forall A B:Prop, A -> A \/ B.
intros.
left.
assumption.

Defined.
Print haha.


Definition deMorgan: 
forall A B:Prop, ~A /\ ~B -> ~(A \/ B) :=
fun A B:Prop =>
fun p:~A /\ ~B =>
fun aorb: A\/B =>
or_ind 
(and_ind (fun (a:~A)(b:~B) => a) p) 
(and_ind (fun (a:~A)(b:~B) => b) p) 
aorb.

Print deMorgan.

Definition demorg:
forall A B:Prop, ~A /\ ~B -> ~(A \/ B) :=
fun A B:Prop =>
and_ind
( fun na:~A => 
  fun nb:~B => 
  fun aorb:A\/B => 
  (or_ind na nb aorb) 
).

Definition ddd:
forall A B:Prop, ~(A \/ B) -> ~A /\ ~B :=
fun A B:Prop =>
fun g: (A \/ B) -> False => (conj
  (fun a:A => g (or_introl a))
  (fun b:B => g (or_intror b))
).





Variable D:Set.
Variable R:D->D->Prop.

Section R_sym_trans.
Hypothesis R_symmetric :
  forall x y : D, R x y -> R y x.
Hypothesis R_transitive :
  forall x y z : D, R x y -> R y z -> R x z.
Lemma refl_if :
  forall x : D, (exists y, R x y) -> R x x.
intros x x_Rlinked.
elim x_Rlinked.
intros y Rxy.
apply R_transitive with y.
exact Rxy.
apply R_symmetric.
exact Rxy.
Qed.
End R_sym_trans.


Variable P :  D -> Prop.
Variable d : D.
Lemma weird : (forall x:D, P x) ->  exists a, P a.
intro UnivP.
exists d.
trivial.
Qed.

Hypothesis EM : forall A : Prop, A \/ ~ A.

Lemma DN : forall A: Prop, ~~A -> A.
intro.
intro nnA.
elim EM with A.
tauto.
intro nA.
elim nnA.
exact nA.
Qed.

Lemma drinker :  exists x : D, P x -> forall x : D, P x.
elim (EM (exists x:D, ~ P x)).

intros (Tom, Tom_does_not_drink).
exists Tom.
intro Tom_drinks.
contradiction.

intro No_nondrinker.
exists d.
intro d_drinks.
intro x.
elim (EM (P x)).
tauto.
intro Dick_does_not_drink.
absurd (exists x:D, ~ P x).
assumption.
exists x.
assumption.
(*
intro.
exists d.
intro.
intro x.
apply (DN (P x)).
intro.
apply H.
exists x.
assumption.
*)
Qed.

End Predicate_calculus.

Section one44.
Variables P Q : nat -> Prop.
Variables R : nat -> nat -> Prop.
Lemma PQR :
  forall x y:nat, (R x x -> P x -> Q x) -> P x -> R x y -> Q x.
intros.
generalize H0.
enough (R x x) by auto.
Abort.


Check refl_if.
Check weird.
Check drinker.

