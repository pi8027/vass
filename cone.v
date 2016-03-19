Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import utils bigop_ext LRA.
Import GRing.Theory Num.Theory.

(******************************************************************************)
(*  Convex cones                                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition pos_cV (R : numDomainType) (d : nat) (m : 'cV[R]_d) :=
  [forall i : 'I_d, 0%R <= m i ord0]%R.

Section ConeDef.

Import GRing.Theory Num.Theory.

Variable (d : nat).

Definition norm_inf (x : 'cV[rat]_d) :=
  \big[Num.max/0%R]_(i < d) `| x i ord0 |%R.

Definition open_set (X : 'cV[rat]_d -> Prop) :=
  forall x,
    X x -> exists2 e : rat,
             (0 < e)%R &
             forall y : 'cV[rat]_d,
               (norm_inf (x - y) < e)%R -> X y.

Definition closure (X : 'cV[rat]_d -> Prop) (y : 'cV_d) :=
  forall e : rat,
    (0 < e)%R ->
    exists2 x : 'cV_d, X x & (norm_inf (y - x) < e)%R.

Definition closed_set (X : 'cV[rat]_d -> Prop) :=
  forall x, closure X x -> X x.

Record cone (C : 'cV[rat]_d -> Prop) := (* cones *)
  {
    cone_zero    : C 0%R;
    cone_add x y : C x -> C y -> C (x + y)%R;
    cone_mul a x : (0 <= a)%R -> C x -> C (a *: x)%R;
  }.

Record fg_cone (C : 'cV[rat]_d -> Prop) := (* finitely generated cones *)
  {
    fg_cone_num     : nat;
    fg_cone_basis   : 'M_(d, fg_cone_num);
    fg_cone_axiom x : C x <->
                      exists2 c : 'cV_fg_cone_num,
                                  pos_cV c & x = (fg_cone_basis *m c)%R
  }.

Record poly_cone (C : 'cV[rat]_d -> Prop) := (* polyhedral cones *)
  {
    poly_cone_num     : nat;
    poly_cone_normal  : 'M_(poly_cone_num, d);
    poly_cone_axiom x : reflect (C x) (pos_cV (poly_cone_normal *m x))
  }.

Definition dual_cone (X : 'cV[rat]_d -> Prop) (y : 'cV[rat]_d) :=
  forall x, X x -> (0 <= (y^T *m x) ord0 ord0)%R.

Lemma dual_cone_is_cone C : cone (dual_cone C).
Proof.
rewrite /dual_cone; constructor => /=.
- by move => x H; rewrite trmx_const mul0mx mxE.
- move => x y Hx Hy z H.
  move: (Hx _ H) (Hy _ H) => {Hx Hy} Hx Hy.
  by rewrite trmxD mulmxDl mxE; apply addr_ge0.
- move => a x Ha H y H0.
  rewrite trmx_scale -scalemxAl mxE.
  by apply mulr_ge0 => //; apply H.
Qed.

Lemma dual_cone_inclusion (C1 C2 : 'cV_d -> Prop) :
  (forall x, C1 x -> C2 x) ->
  forall x, dual_cone C2 x -> dual_cone C1 x.
Proof. by rewrite /dual_cone => H x H0 y /H /H0. Qed.

Lemma dual_cone_closed C : closed_set (dual_cone C).
Proof.
rewrite /closed_set /closure /dual_cone => x H y H0.
apply/negP => /negP; rewrite -ltrNge => H1.
set frac : rat := (\sum_(i < d) `|y i ord0|)%R.
have Hfrac: (0 < frac)%R.
  rewrite ltr_def; apply/andP; split; last by apply sumr_ge0.
  rewrite psumr_eq0 //=; apply/allP => /= H2.
  have {H2} H2 (i : 'I_d) : (y i ord0 = 0)%R
    by apply/eqP; move: (H2 i); rewrite mem_index_enum normr_eq0 => /(_ erefl).
  move: H1; apply/negP; rewrite -lerNgt.
  by rewrite mxE; apply sumr_ge0 => /= i _; rewrite H2 mulr0.
have/H {H} []: (0 < - (x^T *m y) ord0 ord0 / frac)%R
  by apply divr_gt0 => //; rewrite oppr_gt0.
move => x' /(_ y H0) {H0} H H0.
have {H0} H0 i: (`|(x - x') i ord0| < - (x^T *m y) ord0 ord0 / frac)%R
  by apply: (ler_lt_trans _ H0); rewrite /norm_inf -eqr_maxl maxrC -bigD1_l.
move: H; apply/negP; rewrite -ltrNge.
suff: ((x'^T *m y) ord0 ord0 <
       (x^T *m y) ord0 ord0 + (- (x^T *m y) ord0 ord0 / frac) * frac)%R.
  rewrite mulrAC -mulrA divrr; first by rewrite mulr1 subrr.
  by move: Hfrac; rewrite unfold_in /= ltr_def; case/andP.
rewrite mxE {1}mxE -subr_gt0 mulr_sumr -big_split -sumrB /=.
have/(eq_bigr _) -> : forall i, true ->
  (x^T ord0 i * y i ord0 + - (x^T *m y) ord0 ord0 / frac * `|y i ord0| -
   x'^T ord0 i * y i ord0 =
   (x - x') i ord0 * y i ord0 - (x^T *m y) ord0 ord0 / frac * `|y i ord0|)%R
  by move => i _; rewrite addrAC -mulrBl !mxE -!mulNr.
have H i: (0 <= (x - x') i ord0 * y i ord0 -
                (x^T *m y) ord0 ord0 / frac * `|y i ord0|)%R.
  move/(_ i): H0; rewrite ltr_norml mulNr opprK => /andP [] H H0.
  by rewrite subr_ge0 -{1}(subr0 (y _ _)); case: (lerP 0 (y i ord0)) => H2;
    [ rewrite subr0 ler_wpmul2r |
      rewrite sub0r mulrN -mulNr ler_wnmul2r] => //; apply ltrW.
rewrite ltr_def; apply/andP; split; last by apply sumr_ge0.
move/lt0r_neq0: Hfrac; rewrite !psumr_eq0 => // /allPn /= [i H2];
  rewrite normr_eq0 => H3.
apply/allPn; exists i => // {H H2}; rewrite subr_eq0; apply/eqP.
move/(_ i): H0; rewrite ltr_norml mulNr opprK => /andP [H H0].
rewrite -{2}(subr0 (y _ _)); case: (lerP 0 (y i ord0)) => H2.
- by rewrite subr0 => /(mulIf H3); apply/eqP; rewrite neqr_lt H orbT.
- by rewrite sub0r mulrN -mulNr => /(mulIf H3); apply/eqP; rewrite neqr_lt H0.
Qed.

Goal forall C, cone C -> forall x, dual_cone (dual_cone C) x <-> closure C x.
Proof.
move => C [/= HC1 HC2 HC3] x; rewrite /closure /dual_cone; split.
- move => H e H0.
  admit.
- move => H y H0.
  admit.
Abort.

Lemma fg_conic C : fg_cone C -> cone C.
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

Lemma duality_direct C : fg_cone C -> poly_cone C.
Proof.
case => n basis H.
Abort.

Lemma duality_converse C : poly_cone C -> fg_cone C.
Proof.
Abort.

End ConeDef.
