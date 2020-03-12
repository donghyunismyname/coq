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
