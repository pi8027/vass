Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory Num.Theory.

(******************************************************************************)
(*  Vector addition systems                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section VASs.

Variable (dim : nat) (VAS : seq (int ^ dim)).

Definition marking : Type := nat ^ dim.

Definition next (m : marking) (a : int ^ dim) : option marking :=
  if [forall i, 0 <= a i + m i]%R
    then some [ffun i => `|(a i + m i)%R|] else None.

Definition step (m1 m2 : marking) (a : int ^ dim) :=
  [forall i : 'I_dim, a i + m1 i == m2 i]%R.

Lemma next_correct (m1 m2 : marking) a :
  (next m1 a == some m2) = step m1 m2 a.
Proof.
rewrite /next /step; case: ifP; rewrite eqE /= => /forallP H.
- suff ->: forall (f1 f2 : marking), (f1 == f2) = [forall i, f1 i == f2 i]
    by apply eq_forallb => /= i; rewrite ffunE -(gez0_abs (H i)).
  move => f1 f2; apply Bool.eq_iff_eq_true; split.
  + by move/eqP/ffunP => H0; apply/forallP => i; rewrite H0.
  + by move/forallP => H0; apply/eqP/ffunP => i; rewrite (eqP (H0 i)).
- by apply/esym/forallP => /= H0; apply: H => i; rewrite (eqP (H0 i)).
Qed.

Definition run (m : marking) (w : seq (int ^ dim)) : option marking :=
  foldl (fun m' a => obind (next ^~ a) m') (some m) w.

Fixpoint run' (m : marking) (w : seq (int ^ dim)) : option marking :=
  if w is a :: w' then obind (run' ^~ w') (next m a) else some m.

End VASs.
