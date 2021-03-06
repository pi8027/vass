From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp.
Require Import utils bigop_ext matrix_ext.
Import GroupScope Order.TTheory GRing.Theory Num.Theory.

(******************************************************************************)
(*  Convex cones                                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ConeDef.

Variable (d : nat).

Definition norm_inf (x : 'cV[rat]_d) :=
  \big[Num.max/0%R]_(i < d) `| x i 0 |%R.

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

Record cone (C : 'cV[rat]_d -> Prop) := Cone (* cones *)
  {
    cone_zero    : C 0%R;
    cone_add x y : C x -> C y -> C (x + y)%R;
    cone_mul a x : (0 <= a)%R -> C x -> C (a *: x)%R;
  }.

Record fg_cone (C : 'cV[rat]_d -> Prop) :=
  Fg_cone (* finitely generated cones *)
  {
    fg_cone_num     : nat;
    fg_cone_basis   : 'M_(d, fg_cone_num);
    fg_cone_axiom x : C x <->
                      exists2 c : 'cV_fg_cone_num,
                                  posmx c & x = (fg_cone_basis *m c)%R
  }.

Record poly_cone (C : 'cV[rat]_d -> Prop) := Poly_cone (* polyhedral cones *)
  {
    poly_cone_num     : nat;
    poly_cone_normal  : 'M_(poly_cone_num, d);
    poly_cone_axiom x : reflect (C x) (posmx (poly_cone_normal *m x))
  }.

Definition dual_cone (X : 'cV[rat]_d -> Prop) (y : 'cV[rat]_d) :=
  forall x, X x -> posmx (y^T *m x)%R.

Lemma dual_cone_is_cone C : cone (dual_cone C).
Proof.
rewrite /dual_cone; constructor=> /=.
- by move=> x H; rewrite trmx_const mul0mx posmx0.
- move=> x y Hx Hy z H.
  move: (Hx _ H) (Hy _ H) => {}Hx {}Hy.
  by rewrite linearD mulmxDl posmx_add.
- move=> a x Ha H y H0; rewrite linearZ -scalemxAl posmx_mx11 mxE.
  apply: mulr_ge0 => //; rewrite -posmx_mx11; exact: H.
Qed.

Lemma dual_cone_inclusion (C1 C2 : 'cV_d -> Prop) :
  (forall x, C1 x -> C2 x) ->
  forall x, dual_cone C2 x -> dual_cone C1 x.
Proof. by rewrite /dual_cone => H x H0 y /H /H0. Qed.

Lemma dual_cone_closed C : closed_set (dual_cone C).
Proof.
rewrite /closed_set /closure /dual_cone => x H y H0; rewrite posmx_mx11.
apply/negP => /negP; rewrite -ltNge => H1.
set frac : rat := (\sum_(i < d) `|y i 0|)%R.
have Hfrac: (0 < frac)%R.
  rewrite lt_def; apply/andP; split; last exact: sumr_ge0.
  rewrite psumr_eq0 //=; apply/allP => /= H2.
  have {}H2 (i : 'I_d) : (y i 0 = 0)%R
    by apply/eqP; move: (H2 i); rewrite mem_index_enum normr_eq0 => /(_ erefl).
  move: H1; apply/negP; rewrite -leNgt.
  by rewrite mxE; apply: sumr_ge0 => /= i _; rewrite H2 mulr0.
have{}/H []: (0 < - (x^T *m y) 0 0 / frac)%R
  by apply: divr_gt0; rewrite // oppr_gt0.
move=> x' /(_ y H0) H {}H0.
have {}H0 i: (`|(x - x') i 0| < - (x^T *m y) 0 0 / frac)%R
  by apply: (le_lt_trans _ H0); rewrite /norm_inf -eq_joinl joinC -bigD1_l.
move: H; apply/negP; rewrite posmx_mx11 -ltNge.
suff: ((x'^T *m y) 0 0 <
       (x^T *m y) 0 0 + (- (x^T *m y) 0 0 / frac) * frac)%R.
  rewrite mulrAC -mulrA divrr; first by rewrite mulr1 subrr.
  by move: Hfrac; rewrite unfold_in /= lt_def; case/andP.
rewrite mxE {1}mxE -subr_gt0 mulr_sumr -big_split -sumrB /=.
have/(eq_bigr _) -> : forall i, true ->
  (x^T 0 i * y i 0 + - (x^T *m y) 0 0 / frac * `|y i 0| -
   x'^T 0 i * y i 0 =
   (x - x') i 0 * y i 0 - (x^T *m y) 0 0 / frac * `|y i 0|)%R
  by move=> i _; rewrite addrAC -mulrBl !mxE -!mulNr.
have H i: (0 <= (x - x') i 0 * y i 0 -
                (x^T *m y) 0 0 / frac * `|y i 0|)%R.
  move/(_ i): H0; rewrite ltr_norml mulNr opprK => /andP [] H H0.
  rewrite subr_ge0 -{1}(subr0 (y _ _)); case: (lerP 0 (y i 0))%R => H2;
    [ rewrite subr0 ler_wpmul2r // |
      rewrite sub0r mulrN -mulNr ler_wnmul2r //]; exact: ltW.
rewrite lt_def; apply/andP; split; last exact: sumr_ge0.
move/lt0r_neq0: Hfrac; rewrite !psumr_eq0 => // /allPn /= [i H2];
  rewrite normr_eq0 => H3.
apply/allPn; exists i => // {H H2}; rewrite subr_eq0; apply/eqP.
move/(_ i): H0; rewrite ltr_norml mulNr opprK => /andP [H H0].
rewrite -{2}(subr0 (y _ _)); case: (lerP 0 (y i 0%R)) => H2.
- by rewrite subr0 => /(mulIf H3); apply/eqP; rewrite neq_lt H orbT.
- by rewrite sub0r mulrN -mulNr => /(mulIf H3); apply/eqP; rewrite neq_lt H0.
Qed.

Lemma dual_coneK C : poly_cone C -> forall x, C x <-> dual_cone (dual_cone C) x.
Proof.
move=> [n normal Hpoly] x; split;
  first by move=> H y /(_ _ H); rewrite mulmx_trl posmx_trmx.
rewrite /dual_cone => H; apply/Hpoly/posmxP => i j.
rewrite mulmx_row_col col_id -posmx_mx11 -posmx_trmx trmx_mul {j}.
by apply: H => x' /Hpoly /posmxP /(_ i 0%R);
  rewrite trmxK mulmx_row_col col_id -posmx_mx11.
Qed.

Lemma fg_conic C : fg_cone C -> cone C.
Proof.
case=> basis_num basis axiom; constructor.
- apply/axiom; exists (\col__ 0%Q)%R; first by apply/posmxP => i j; rewrite mxE.
  by apply/matrixP => i j; rewrite !mxE; apply/esym/eqP; rewrite psumr_eq0 /=;
    [apply/allP |]; move=> /= k _; rewrite mxE mulr0.
- move=> x y /axiom [cx /posmxP Hx ->] /axiom [cy /posmxP Hy ->].
  apply/axiom; exists (cx + cy)%R; last by rewrite mulmxDr.
  apply/posmxP => i j; rewrite mxE; exact: ler_paddl.
- move=> /= a x H /axiom [c /posmxP Hc ->].
  apply/axiom; exists (a *: c)%R; last by rewrite scalemxAr.
  apply/posmxP => i j; rewrite mxE; exact: mulr_ge0.
Qed.

(* duality *)

Lemma duality_direct C : fg_cone C -> poly_cone C.
Proof.
case=> n basis H.
set A := (col_mx (row_mx 1%:M 0) (block_mx (- basis) 1%:M basis (- 1%:M)))%R.
have HC (x : 'cV_d) (c : 'cV_n):
  (posmx (A *m col_mx c x))%R = (posmx c && (x == basis *m c))%R by
  rewrite /A /block_mx -(opprK (row_mx basis _)) opp_row_mx opprK !mul_col_mx
             !posmx_col mulNmx eq0mx_posmx !mul_row_col !mul_scalar_mx !scale1r
             (addrC _ x) mulNmx subr_eq0 -{3}(addr0 c);
    congr (posmx (_ + _)%R && _); apply/matrixP => i j; rewrite !mxE /=;
    apply big_rec => // k y _ -> {y}; rewrite !mxE mul0r.
apply: (@Poly_cone C _ (tagged (Fourier_Motzkin_m A))) => x; apply/(iffP idP).
- by case/Fourier_Motzkin_mP => c;
    rewrite HC => /andP [] H0 /eqP ->; apply/H; exists c.
- by case/H => c H0 ->; apply/Fourier_Motzkin_mP; exists c; rewrite HC H0 eqxx.
Qed.

Lemma dual_of_poly_cone C : poly_cone C -> fg_cone (dual_cone C).
Proof.
case=> n normal Hpoly; apply: (@Fg_cone _ _ normal^T)%R => y; split.
- rewrite/dual_cone => H; apply/Farkas => x.
  rewrite -trmx_mul mulmx_trl !posmx_trmx => /Hpoly; exact: H.
- case=> c /posmxP H -> {y} x /Hpoly /posmxP H0.
  rewrite posmx_mx11 trmx_mul trmxK -mulmxA mxE.
  by apply: sumr_ge0 => /= i _; apply: mulr_ge0; rewrite // mxE.
Qed.

Lemma duality_converse C : poly_cone C -> fg_cone C.
Proof.
move=> H0; have H := dual_coneK H0.
case/dual_of_poly_cone/duality_direct/dual_of_poly_cone: H0 => n basis H0.
by apply: (@Fg_cone _ _ basis) => x; split=> [/H /H0 | /H0 /H].
Qed.

End ConeDef.
