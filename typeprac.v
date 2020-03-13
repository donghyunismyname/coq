Print sigT.
Check existT.

Variable A B:Type.
Variable P:A->B->Type.


Theorem aaa: {a:A & forall b:B, P a b} -> forall b:B, {a:A & P a b}.
Proof.
  intros.
  destruct X.
  exists x.
  apply p.
Qed.

Print aaa.
  