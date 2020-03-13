Require Import PeanoNat.
Local Open Scope nat_scope.


Inductive natlist:Set :=
| empty : natlist
| cons: nat -> natlist -> natlist.


Check (cons 10 (cons 20 empty)).