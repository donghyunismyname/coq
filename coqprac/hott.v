Section practice.


Variable sig: forall A:Type, (A->Type) -> Type.



Variable A:Type.
Variable B:A -> Type.

Variable ind: 
forall C: (sig A B) -> Type,
(forall a:A, forall b:B a, C (a,b)) 
->
(forall p: (sig A B), C p).