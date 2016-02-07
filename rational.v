Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import LRA.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition pos_cV (d : nat) (m : 'cV[rat]_d) :=
  [forall i : 'I_d, 0%Q <= m i ord0]%R.

Section rational.

Variable (d : nat).

Record conic_set (C : 'cV_d -> bool) :=
  { conic_set_zero : C (\col__ 0%Q)%R;
    conic_set_add  : forall x y, C x -> C y -> C (x + y)%R;
    conic_set_mul  : forall a x, (0 <= a)%R -> C x -> C (a *: x)%R;
  }.

Record conic_set_fg (C : 'cV_d -> bool) := (* finitely generated *)
  { basis_num          : nat;
    basis              : 'M_(d, basis_num);
    conic_set_fg_axiom :
      forall x, C x <->
                exists2 c : 'cV_basis_num, pos_cV c & x = (basis *m c)%R
  }.

Lemma fg_conic C : conic_set_fg C -> conic_set C.
Proof.
  case => basis_num basis axiom; constructor.
  - apply axiom; exists (\col__ 0%Q)%R.
    + by apply/forallP => /= i; rewrite mxE.
    + apply/matrixP => i j.
      by rewrite !mxE; apply/esym/eqP; rewrite psumr_eq0 /=;
        [apply/allP |]; move => /= k _; rewrite mxE mulr0.
  - move => x y /axiom [cx /forallP /= Hx ->]
                /axiom [cy /forallP /= Hy ->]; apply axiom.
    exists (cx + cy)%R.
    + apply/forallP => /= i; rewrite mxE; apply ler_paddl => //.
    + by rewrite mulmxDr.
  - move => /= a x H /axiom [c /forallP /= Hc ->]; apply axiom.
    exists (a *: c)%R.
    + by apply/forallP => /= i; rewrite mxE; apply mulr_ge0.
    + by rewrite scalemxAr.
Qed.

Definition norm_inf (x : 'cV[rat]_d) :=
  \big[Num.Def.maxr/0%R]_(i < d) `| x i ord0 |%R.

Definition closure (X : 'cV[rat]_d -> Prop) (x : 'cV_d) :=
  forall e : rat, exists y : 'cV_d, (norm_inf (x + y) < e)%R.

Lemma Farkas m n (A : 'M[rat]_(m, n)) (b : 'cV[rat]_m) :
  (exists2 x : 'cV[rat]_n, A *m x = b & pos_cV x)%R \/
  ().

Lemma duality_direct C :
  conic_set_fg C ->
  exists H : seq (rat ^ dim), forall x : rat ^ dim,
     C x <-> all (fun h => 0 <= )%R H).

Lemma duality_converse C :
  conic_set C ->
  (exists H : seq (rat ^ dim), forall x : rat ^ dim,
      C x <-> all (fun h => 0 <= )%R H) ->
  conic_set_fg C.




(*
End rational.

********************************************************************************
*)
