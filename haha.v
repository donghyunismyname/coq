Print eq_ind.
Print nat_rect.
Print nat_rec.

Definition ntp:nat->Prop :=
  nat_rect (fun _:nat => Prop)
           True
           (fun (_:nat)(_:Type) => False).

Definition zero_neq_one : 0 <> 1 :=
  fun pf:0=1 => eq_ind 0 ntp I 1 pf.

Definition zero_neq_successor: forall n:nat, 0 <> S n .
  induction n.
  exact zero_neq_one.
  
  



Print le.
Print le_ind.

Definition donghyun: not (1 <= 0).
  intro. inversion H.
Qed.

Print donghyun.


Goal forall a:nat, a <= 0 -> a = 0.
  
  
  

Goal forall a b:nat, a<=b -> exists k, a+k=b.
  intro a. induction b.
  - in

Goal forall a b:nat, a <= b <-> exists d, a+d=b.
  induction a. induction b.
  split.
  + intro. exists 0. reflexivity.
  + intro. apply le_n.
  + split.
    intro.
      



Goal 10=10.
reflexivity.
Qed.
Goal 1=1.
reflexivity.
Qed.
Goal 1=1.
reflexivity.
Qed.


Print eq_ind.

Definition inv : forall (A:Type)(a b:A), a=b -> b=a :=
  fun A a b e => eq_ind a
                        (fun x => x=a)
                        eq_refl
                        b
                        e.

Definition compo : forall (A:Type)(a b c:A), a=b -> b=c -> a=c :=
  fun A a b c eab ebc => eq_ind b
                                (fun x => a=x)
                                eab
                                c
                                ebc.

Variable A:Type.
Variable x y z w:A.
Variable p:x=y.
Variable q:y=z.
Variable r:z=w.

Definition com : forall {a b c:A}, a=b -> b=c -> a=c :=
  compo A.
Notation "x * y" := (com x y).
                                                   

Definition fufu: p*(q*p) = (p*q)*p  := eq_refl.






Definition add : nat->nat->nat :=
  fun a => nat_rec (fun _=>nat) a (fun (_:nat)(x:nat) => S x).

Print eq_rect.



Definition aaa: forall n:nat, add 0 n = add n 0 :=
  nat_ind
    (fun n => add 0 n = add n 0)
    eq_refl
    (fun n e =>
       eq_ind (add 0 n)
              (fun x => S (add 0 n) = S (x))
              eq_refl
              (add n 0)
              e).


Compute (aaa 10).
Compute (aaa 0).

Definition pr1:nat->nat->nat.
  intro. intro. exact H.
Qed.

Definition prr:nat->nat->nat := fun a b => a.

Compute (prr 11 22).



    
Variable A:Type.
Variable B:A->Type.
Variable C:{x:A & B x} -> Type.

Definition ac:
  (forall x:A, {b:B x & C (existT B x b)}) ->
  {g:(forall x:A, B x) & forall x:A, C (existT B x (g x))}
  :=
    fun f => existT
               (fun g:(forall x:A, B x) => forall x:A, C (existT B x (g x)))
               (fun x:A => projT1 (f x))
               (fun x:A => projT2 (f x)).
    
  



Variable A B C:Type.
Variable P: A->B->Type.

Print existT.
Print projT2.

Definition aaa:
  {a:A & forall b:B, P a b} -> forall b:B, {a:A & P a b} :=
fun u b => existT 
  (fun a => P a b)
  (projT1 u)
  (projT2 u b).




Variable A:Type.
Variable B:A->Type.
Variable C:{a:A & B a} -> Type.

Definition aaa : 
  (forall x:A, forall y:(B x), C (existT B x y))
  -> forall f:(forall x:A, B x), forall x:A, C (existT B x (f x)) 
:=
  fun p f x => p x (f x).






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
