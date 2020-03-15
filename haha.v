Variable A B C:Type.
Variable P: A->B->Type.








Print sigT.

Print sigT_rect.

Print projT1.

Variable A:Type.
Variable B:A->Type.


Definition C1 : {a:A & B a}  -> Type := 
  fun (_:{a:A & B a}) => A.
Definition g1 : forall a:A, forall b:(B a), C1 (existT B a b) :=
  fun (a:A)(b:(B a)) => a.
Definition pr1 : {a:A & B a} -> A :=
  sigT_rect C1 g1.


Definition C2 : {a:A & B a} -> Type := 
  fun (p:{a:A & B a}) => B (pr1 p).
Definition g2 : forall a:A, forall b:(B a), C2 (existT B a b) :=
  fun (a:A)(b:(B a)) => b.
Definition pr2 : forall p:{a:A & B a}, B (pr1 p) :=
  sigT_rect C2 g2.


Variable a:A.
Variable b:B a.
Variable C:{a:A & B a} -> Type.
Variable g: forall a:A, forall b:(B a), C (existT B a b).
Variable p:{a:A & B a}.
Compute (pr1 (existT B a b)).
Compute (pr2 (existT B a b)).
Compute (pr1 p).
Compute (sigT_rect C g (existT B a b)).
Compute (sigT_rect C g p).


Compute projT1 p.
Theorem aaa: @projT1 A B = pr1.
Proof.
  reflexivity.
Qed.

Print aaa.

Theorem bbb: @projT2 A B = pr2.
reflexivity.
Qed.

Theorem xxx: forall f:Type->Type, f = (fun a => f a).
intros.
reflexivity.
Qed.


Theorem ccc: p = (existT B (pr1 p) (pr2 p)).

reflexivity.

unfold pr1, pr2.







Inductive li (A:Type) :Type :=
| nil: li A
| cons: A -> li A -> li A.

Check li.
Check li_rect.
Check cons.
Check nil.

Inductive even : nat -> Type :=
| ev_0 : even 0
| ev_SS : forall (n:nat)(H:even n), even (S (S n)).

Check even_rect.
Check even.

Definition aa:even 4 :=
ev_SS 2 (ev_SS 0 ev_0).


Variable A:Type.
Variable B:A->Type.
Variable C:(sigT B) -> Type.

Print sigT.
Print existT.
Check existT .
Print sigT_rect.

Check projT1.
Print projT1.

Check fun (a:A) => a.
Check fun (a:A) (b:B a) => (existT B a b).

Check fun (p:{a:A & B a}) => Type.

Definition ind: 
forall a:A, forall b:(B a), C





Variable A:Type.


Variable ind:
forall C:(forall (x y:A) (p:x=y), Type),
(forall x:A, C x x eq_refl)
->
(forall (x y:A) (p:x=y), C x y p).



Definition indb:
forall a:A,
forall D:(forall x:A, a=x -> Type),
(D a eq_refl)
->
(forall (x:A) (p:a=x), D x p)
:=
fun (a:A) (D:forall x:A, a=x -> Type) 
(d: D a eq_refl)
(x:A) (p:a=x)
=>
ind 
(fun (x y:A)(q:x=y) => D x p).





Definition symm:
forall x y:A, x=y -> y=x :=
ind 
(fun (x y:A) (p:x=y) => y=x)
(fun (x:A) => eq_refl).

Definition trans:
forall x y z:A, x=y -> y=z -> x=z :=
