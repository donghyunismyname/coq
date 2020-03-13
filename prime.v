Fixpoint eqb (a b:nat):bool :=
  match a, b with
  | 0, 0 => true
  | S aa, S bb => eqb aa bb
  | _, _ => false
  end.

Notation "a =? b" := (eqb a b) (at level 10).

Lemma eqb_eq: forall a b:nat, a =? b = true <-> a = b.
Proof.
  induction a.
  - destruct b.
    + split. auto. auto.
    + split. intro. inversion H. intro. inversion H.
  - destruct b.
    + split. intro. inversion H. intro. inversion H.
    + simpl. split.
      * intro.
        enough (a=b). rewrite H0. reflexivity.
        apply IHa. apply H.
      * intro.
        apply IHa.
        inversion H.
        reflexivity.
Qed.



Fixpoint leb (a b:nat):bool :=
  match a, b with
  | 0, _ => true
  | S aa, 0 => false
  | S aa, S bb => leb aa bb
  end.

Notation "a <=? b" := (leb a b) (at level 10).

Lemma sdds: forall a b:nat, a <= b <-> S a <= S b.
Proof.
  

      
        
    
    
    
  
Lemma le_prop: forall a b:nat, a <? b = true  <-> a < b.
Proof.
  split.
  - induction b.
    + enough (forall x:nat, x <? 0 = false).
      rewrite H. intro. inversion H0.
      induction x. reflexivity. simpl. reflexivity.
    + intro.
      
    
Fixpoint rem (a d:nat):nat :=
  match a with
  | 0 => 0
  | S aa => let r := S (rem aa d) in
            if (equal r d) then 0 else r
  end.


Lemma rem_property:
  forall a d r:nat,
    d<>0 -> (rem a d)=r <-> exists q, a = q*d + r /\ 0 <= r /\ r < d.
Proof.
  intros.
  



Definition div(d a:nat):bool :=
  equal 0 (rem a d).

Fixpoint hasdivisor (n d:nat) :=
  match d with
  | 0 => true
  | 1 => false
  | S dd => if (div d n)
            then true
            else hasdivisor n dd
  end.



        
    

    

  
Corollary rem_by_itself_equals_zero: forall n:nat, rem n n = 0.
  
  
  induction n. reflexivity.
  simpl.
  enough (forall a:nat, rem a (S a) = a).
  + rewrite H. 
    enough (forall n:nat, equal n n = true).
    * rewrite H0. reflexivity.
    * induction n0. reflexivity.
      simpl. rewrite IHn0. reflexivity.
  + induction a. reflexivity.
    simpl.
    assert (rem a (S (S a)) = a).
    * unfold rem.
   

    
      
      



      Lemma sdfas: forall n, div n n = true.
  induction n.
  - reflexivity.
  - unfold div in IHn.
    unfold div.
    simpl.
  


Lemma aaaaa: forall n:nat, n>1 -> (exists d, hasdivisor n d = true) -> (exists d:nat, (1<d) /\ (div d n) = true).
  intros.
  exists n.
  split.
  - exact H.
  - reflexivity.





Definition isprime (n:nat) :=
  match n with
  | 0 => false
  | 1 => false
  | S nn =>  if hasdivisor n nn
             then false
             else true
  end.


Lemma haha: forall n:nat,
  isprime n = true
  <->
  exists d:nat, (1<d) /\ (d<n) /\ (div d n) = true.
Proof.
  induction n.
  simpl.
  split.
  intro.
  inversion H.
  intros.
  inversion H.
  inversion H0.
  inversion H2.
  inversion H3.

  induction n.
  simpl.
  split.
  intros.
  inversion H.
  intros.
  inversion H.
  inversion H0.
  inversion H2.
  inversion H3.
  rewrite H6 in H1.
  inversion H1.
  inversion H6.

  split.
  Focus 2.
intros.


inversion H.
simpl.



