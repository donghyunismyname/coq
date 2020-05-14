Inductive list (A:Type) :=
| nil : list A
| cons : A -> (list A) -> (list A).


Check nil.




Definition Group := {G:Type & {op:G->G->G & forall }}.

Print Group.




Definition category
           (Obj:Type)
           (id: forall A:Obj, A->A)
           (compo: forall A B C:Obj, forall f:A->B, forall g:B->C, A->C) :=
  (forall A B:Obj, forall f:A->B, 




Definition category (Obj Arr:Type) (dom cod:Arr->Obj) (id:Obj->Arr) (compo:Arr->Arr->Arr) :=
  (forall f:Arr, forall A B:Obj, dom f = A -> cod f = B -> compo f (id A) = f /\ compo (id B) f = f) /\
  (forall f g h:Arr, forall A B C D
