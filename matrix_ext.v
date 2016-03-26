Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp.
Import GroupScope GRing.Theory Num.Theory.
Require Import utils.

(******************************************************************************)
(*  extensions for matrix                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma trmxD (R : zmodType) m n : {morph @trmx R m n : x y / (x + y)}%R.
Proof. by move => x y; apply/matrixP => i j; rewrite !mxE. Qed.

Lemma trmx_scale (R : ringType) m n (a : R) :
  {morph @trmx _ m n : x / (a *: x)}%R.
Proof. by move => x; apply/matrixP => i j; rewrite !mxE. Qed.

(* pointwise comparison for matrices *)

Section lermx.

Variable (R : numDomainType).

Section lermx_def.

Variable (m n : nat).

Definition lermx (mx1 mx2 : 'M[R]_(m, n)) :=
  [forall i : 'I_m * 'I_n, mx1 i.1 i.2 <= mx2 i.1 i.2]%R.

Definition posmx (mx : 'M[R]_(m, n)) := lermx 0 mx.

Lemma lermxP (mx1 mx2 : 'M[R]_(m, n)) :
  reflect (forall i j, mx1 i j <= mx2 i j)%R (lermx mx1 mx2).
Proof. by apply (iffP forallP) => //= H i j; apply (H (i, j)). Qed.

Lemma posmxP (mx : 'M[R]_(m, n)) :
  reflect (forall i j, 0 <= mx i j)%R (posmx mx).
Proof.
  by apply (iffP (lermxP 0 mx)) => H i j; move: (H i j); rewrite mxE.
Qed.

End lermx_def.

Notation "A <=m B" := (lermx A B) (at level 70, no associativity) : ring_scope.

Lemma lermx_col m1 m2 n (mx1 mx1' : 'M_(m1, n)) (mx2 mx2' : 'M_(m2, n)) :
  (col_mx mx1 mx2 <=m col_mx mx1' mx2' = (mx1 <=m mx1') && (mx2 <=m mx2'))%R.
Proof.
apply/lermxP; case: andP.
- by case => /lermxP H /lermxP H0 i j; rewrite !mxE; case: splitP.
- move => H H0; apply: H; split; apply/lermxP => i j.
  + by move: (H0 (lshift m2 i) j); rewrite !col_mxEu.
  + by move: (H0 (rshift m1 i) j); rewrite !col_mxEd.
Qed.

Lemma lermx_row m n1 n2 (mx1 mx1' : 'M_(m, n1)) (mx2 mx2' : 'M_(m, n2)) :
  (row_mx mx1 mx2 <=m row_mx mx1' mx2' = (mx1 <=m mx1') && (mx2 <=m mx2'))%R.
Proof.
apply/lermxP; case:andP.
- by case => /lermxP H /lermxP H0 i j; rewrite !mxE; case: splitP.
- move => H H0; apply: H; split; apply/lermxP => i j.
  + by move: (H0 i (lshift n2 j)); rewrite !row_mxEl.
  + by move: (H0 i (rshift n1 j)); rewrite !row_mxEr.
Qed.

Lemma posmx_col m1 m2 n (mx1 : 'M_(m1, n)) (mx2 : 'M_(m2, n)) :
  posmx (col_mx mx1 mx2) = posmx mx1 && posmx mx2.
Proof. by rewrite /posmx {1}/GRing.zero /= -col_mx_const lermx_col. Qed.

Lemma posmx_row m n1 n2 (mx1 : 'M_(m, n1)) (mx2 : 'M_(m, n2)) :
  posmx (row_mx mx1 mx2) = posmx mx1 && posmx mx2.
Proof. by rewrite /posmx {1}/GRing.zero /= -row_mx_const lermx_row. Qed.

Lemma posmx_mulP m n p (mx1 : 'M_(m, n)) (mx2 : 'M_(n, p)) :
  reflect (forall i j, 0 <= (row i mx1 *m col j mx2) 0 0)%R
          (posmx (mx1 *m mx2)).
Proof.
  by apply/(iffP (posmxP _)) => H i j; move: {H} (H i j);
    rewrite !mxE; congr (_ <= _)%R; apply eq_bigr => k _; rewrite !mxE.
Qed.

Lemma eq0mx_posmx m n (mx : 'M_(m, n)) :
  posmx mx && posmx (- mx)%R = (mx == 0%R).
Proof.
apply/andP; case: eqP.
- by move => ->; rewrite oppr0; split; apply/posmxP => i j; rewrite mxE.
- move => H [] /posmxP H0 /posmxP H1; apply: H; apply/matrixP => i j; apply/eqP.
  by move: (H0 i j) (H1 i j); rewrite !mxE oppr_ge0 eqr_le => -> ->.
Qed.

End lermx.

Notation "A <=m B" := (lermx A B) (at level 70, no associativity) : ring_scope.

(* row/column filtering *)

Section filter_matrix.

Variable (R : Type) (m n : nat).
Variable (P : pred 'rV[R]_n) (A : 'M[R]_(m, n)).

Definition filter_mx : 'M[R]_(#|[pred i : 'I_m | P (row i A)]|, n) :=
  (\matrix_i row (enum_val i) A)%R.

Lemma filter_mxE1 i : row i filter_mx = row (enum_val i) A.
Proof. by rewrite rowK. Qed.

Lemma filter_mxE2 (i : 'I_m) (H : P (row i A)) :
   row i A = row (enum_rank_in H i) filter_mx.
Proof. by rewrite rowK enum_rankK_in. Qed.

Lemma filter_mxT i : P (row i filter_mx).
Proof. by rewrite rowK; move: (enum_valP i); rewrite unfold_in. Qed.

End filter_matrix.

(* Fourier-Motzkin variable elimination for matrix inequation 0 <= A x *)

Module Fourier_Motzkin.
Section Fourier_Motzkin.

Variable (R : realFieldType) (m n : nat) (A : 'M[R]_(m, 1 + n)).

Definition P0 (r : 'rV[R]_(1 + n)) := (r 0 0 == 0)%R.
Definition Ppos (r : 'rV[R]_(1 + n)) := (0 < r 0 0)%R.
Definition Pneg (r : 'rV[R]_(1 + n)) := (r 0 0 < 0)%R.

Definition subA0 := filter_mx P0 A.
Definition subApos := filter_mx Ppos A.
Definition subAneg := filter_mx Pneg A.

Definition fm :
  'M[R]_(#|[pred i | P0 (row i A)]| +
         #|[pred i | Ppos (row i A)]| * #|[pred i | Pneg (row i A)]|, n) :=
  col_mx (rsubmx subA0)
         (\matrix_i' mxvec
           (\matrix_(i, j)
             (subApos i 0 *: rsubmx (row j subAneg) -
              subAneg j 0 *: rsubmx (row i subApos))) 0 i')%R.

Lemma fmP (x : 'cV[R]_n) :
  reflect (exists x0, posmx (A *m (col_mx (const_mx x0) x)))%R
          (posmx (fm *m x))%R.
Proof.
rewrite mul_col_mx posmx_col.
have H_A0 i : subA0 i 0%R = 0%R
  by move/eqP: (filter_mxT (A := A) (P := P0) i); rewrite /P0 mxE.
have H_pos i : (0 < subApos i 0)%R
  by move: (filter_mxT (A := A) (P := Ppos) i); rewrite /Ppos mxE.
have H_neg i : (subAneg i 0 < 0)%R
  by move: (filter_mxT (A := A) (P := Pneg) i); rewrite /Pneg mxE.
have ->: posmx (\matrix_i' (mxvec
                 (\matrix_(i, j) (subApos i 0 *: rsubmx (row j subAneg) -
                                  subAneg j 0 *: rsubmx (row i subApos))%R))
                 0%R i' *m x) =
         [forall i, (subAneg i.2 0 * (rsubmx (row i.1 subApos) *m x) 0 0 <=
                     subApos i.1 0 * (rsubmx (row i.2 subAneg) *m x) 0 0)%R].
  apply/posmx_mulP; case: forallP => /=.
  - move => H i j; rewrite ord1 rowK {j}.
    case (curry_mxvec_bij #|[pred i | Ppos (row i A)]|
                          #|[pred i | Pneg (row i A)]|) => inv _ H0.
    rewrite -(H0 i) /=; case: (inv i) => //= {i inv H0} i j.
    by rewrite mxvecE (mxE _ _ i j) col_id mulmxBl mxE (mxE oppmx_key)
               subr_ge0 -!scalemxAl !(mxE scalemx_key) (H (i, j)).
  - move => H' H; apply: H' => -[i j] /=; move: {H} (H (mxvec_index i j) 0%R).
    by rewrite rowK mxvecE mxE col_id mulmxBl
               mxE (mxE (oppmx_key)) subr_ge0 -!scalemxAl !(mxE scalemx_key).
have H_A0E x0: posmx (rsubmx subA0 *m x) =
              posmx (subA0 *m col_mx (const_mx (m := 1) x0) x).
  congr posmx; apply/esym; rewrite -{1}(hsubmxK subA0) mul_row_col.
  suff ->: lsubmx subA0 = 0%R by rewrite mul0mx add0r.
  apply/esym/matrixP => i j; rewrite ord1 2!mxE -(H_A0 i) {j}.
  by congr (subA0 _ _); apply/val_inj.
have {H_A0E} H_decomp_ineq x0:
  posmx (A *m col_mx (const_mx (m := 1) x0) x) =
  [&& posmx (rsubmx subA0 *m x),
      posmx (subApos *m col_mx (const_mx (m := 1) x0) x) &
      posmx (subAneg *m col_mx (const_mx (m := 1) x0) x)].
  rewrite (H_A0E x0); apply/posmx_mulP; case: and3P;
    last by move => H H0; apply: H; split;
            apply/posmx_mulP => i j; move: H0; rewrite filter_mxE1.
  by case => H H0 H1 i j; case: (ltrgtP 0%R (row i A 0 0)%R);
    last move/esym/eqP; move => H2;
    rewrite 1?(filter_mxE2 (P := P0) H2)
            1?(filter_mxE2 (P := Ppos) H2)
            1?(filter_mxE2 (P := Pneg) H2);
    move: (enum_rank_in _ _) j; apply/posmx_mulP.
apply/(iffP andP).
- case => H /forallP /= H0.
  suff {H H_decomp_ineq}:
    exists x0, posmx (subApos *m col_mx (const_mx x0) x) &&
               posmx (subAneg *m col_mx (const_mx x0) x)
    by case => x0 H1; exists x0; rewrite H_decomp_ineq H H1.
  have: let b (r : 'rV_(1 + n)) := (- (rsubmx r *m x) 0 0 / r 0 0)%R in
        itv_isnot0
          (\big[itv_intersection/itv1]_
            (i : 'I_#|[pred i | Ppos (row i A)]| +
                 'I_#|[pred i | Pneg (row i A)]|)
            match i with
              | inl i => `[b (row i subApos), +oo[%R
              | inr j => `]-oo, b (row j subAneg)]%R
            end)
    by rewrite /= itv_intersection_isnot0E;
      apply/all_allpairsP => -[] /= i [] j _ _ //=; first (by case: ifP);
      rewrite !mulNr ler_opp2 !(mxE matrix_key _ 0%R);
      [move: (H0 (i, j)) | move: (H0 (j, i))];
      rewrite /= !(mulrC _ (_ 0 0)%R) ler_pdivl_mulr // mulrAC ler_ndivr_mulr.
  rewrite /= big_sumType /=.
  case/itv_isnot0P => /= x0; rewrite itv_intersectionE -!itv_bigIE
    => /= /andP [] /allP /= H1 /allP /= H2; exists x0.
  apply/andP; split; apply/posmx_mulP => i j;
    rewrite ord1 {j} col_id -(hsubmxK (row i _)) mul_row_col 2!mxE big_ord1
            2!mxE (mxE const_mx_key) (val_inj _ _ _ : lshift n 0 = 0)%R //
            ?(addrC (subAneg _ _ * _)%R) -[X in (_ + X)%R]opprK subr_ge0
            -?mulNr mulrC; first rewrite -ler_pdivr_mulr //;
                           last rewrite -ler_pdivl_mulr ?oppr_gt0 //.
  + by move: (H1 i); rewrite mem_index_enum inE andbT => /(_ erefl);
      congr (- _ / _ <= _)%R; rewrite !mxE.
  + rewrite invrN mulrN -mulNr.
    by move: (H2 i); rewrite mem_index_enum inE => /(_ erefl);
      congr (_ <= - _ / _)%R; rewrite mxE.
- case => x0; rewrite {}H_decomp_ineq => /and3P [H Hpos Hneg]; split => // {H}.
  apply/forallP => -[/= i j].
  move: (posmx_mulP _ _ Hpos i 0%R) (posmx_mulP _ _ Hneg j 0%R).
  rewrite !col_id -{1}(hsubmxK (row i subApos)) -{1}(hsubmxK (row j subAneg))
          !mul_row_col !(mxE addmx_key) ![(lsubmx _ *m _)%R _ _]mxE !big_ord1
          !(mxE lsubmx_key) ![row _ _ _ _]mxE ![const_mx _ _ _]mxE
          (_ : lshift n 0 = 0)%R; last by apply/val_inj.
  rewrite !(addrC (_ * _)%R);
    do 2 rewrite -{1}[X in (_ + X)%R](opprK (_ * _))%R subr_ge0.
  by rewrite -(ler_nmul2l (H_neg j)) -(ler_pmul2l (H_pos i) (- _)%R)
             -!mulrN mulrCA; apply ler_trans.
Qed.

End Fourier_Motzkin.
End Fourier_Motzkin.

Definition Fourier_Motzkin := Fourier_Motzkin.fm.

Definition Fourier_MotzkinP
      (R : realFieldType) (m n : nat) (A : 'M[R]_(m, 1 + n)) (x : 'cV[R]_n) :
  reflect (exists x0, posmx (A *m (col_mx (const_mx x0) x)))%R
          (posmx (Fourier_Motzkin A *m x))%R := Fourier_Motzkin.fmP _ _.

Fixpoint Fourier_Motzkin_m (R : realFieldType) (m n1 n2 : nat) :
  'M[R]_(m, n1 + n2) -> {r : nat & 'M_(r, n2)} :=
  match n1 with
  | 0 => fun (A : 'M_(m, n2)) => Tagged (fun r => 'M_(r, n2)) A
  | n1'.+1 => fun A => Fourier_Motzkin_m (Fourier_Motzkin A)
  end.

Lemma Fourier_Motzkin_mP (R : realFieldType) (m n1 n2 : nat)
      (A : 'M[R]_(m, n1 + n2)) (y : 'cV[R]_n2) :
  reflect (exists x, posmx (A *m (col_mx x y)))
          (posmx (tagged (Fourier_Motzkin_m A) *m y)).
Proof.
elim: n1 m A => [| n IHn] m A.
- by apply/(iffP (posmx_mulP _ _));
    [move => /= H; exists (const_mx 0%R); apply/posmx_mulP |
     case => x /posmx_mulP H];
    move => i j; move: {H} (H i j); rewrite !col_id !mxE /= {j};
    congr (_ <= _)%R; apply eq_bigr => j _; rewrite !mxE;
    (case: splitP; first case => //) => j' H;
    congr (_ * y _ _)%R; apply/val_inj.
- apply(iffP (IHn _ (Fourier_Motzkin A))).
  + case => x /Fourier_MotzkinP [x0 H].
    exists (col_mx (m1 := 1) (const_mx x0) x).
    by move: H; rewrite col_mxA; congr (posmx (_ *m _)%R); rewrite castmx_id.
  + case => x H; exists (dsubmx (m1 := 1) x); apply/Fourier_MotzkinP.
    exists (x 0 0)%R; move: H; congr (posmx (A *m _)).
    rewrite col_mxA castmx_id.
    suff ->: const_mx (x 0%R 0%R) = usubmx (m1 := 1) x by rewrite vsubmxK.
    by apply/matrixP => i j; rewrite !mxE;
      congr (x _ _); apply/val_inj => /=; rewrite ord1.
Qed.

(* Farkas' lemma *)

Lemma Farkas_subproof (R : numDomainType) m n (A : 'M[R]_(m, n)) (b : 'cV_m) :
  (exists x : 'cV_n, (A *m x) <=m b)%R <->
  (forall y : 'cV_m, posmx y -> A^T *m y = 0 -> 0 <= (y^T *m b) 0 0)%R.
Proof.
split.
- case => x /lermxP H y /posmxP /= H0 H1.
  have ->: (0 = (y^T *m (A *m x)) 0 0)%R
    by rewrite mulmxA -(trmxK (y^T *m _))%R
               trmx_mul trmxK H1 trmx0 mul0mx mxE.
  rewrite -subr_ge0.
  have <- : ((y^T *m (b - (A *m x))) 0 0 =
             (y^T *m b) 0 0 - (y^T *m (A *m x)) 0 0)%R
    by rewrite mulmxBr mxE (mxE oppmx_key).
  by rewrite mxE /=; apply sumr_ge0 => i _; rewrite 3!mxE;
     apply mulr_ge0 => //; rewrite subr_ge0.
-
Abort.
