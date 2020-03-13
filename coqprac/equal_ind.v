Section prac.

Variable A:Type.
Variable ind1:
forall C:(forall x y:A, x=y -> Type),
(forall x:A, (C x x eq_refl)) ->
forall x y:A, forall p:x=y, (C x y p).

Definition symm: forall x y:A, x=y -> y=x.
apply ind1.
intro.
apply eq_refl.
Qed.
Print symm.


Definition trans: forall x y z:A, x=y -> y=z -> x=z.
intros x y z.
apply ind1.