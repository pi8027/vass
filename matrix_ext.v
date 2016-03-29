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

Lemma trmxN (R : zmodType) m n : {morph @trmx R m n : x / - x}%R.
Proof. by move => x; apply/matrixP => i j; rewrite !mxE. Qed.

Lemma trmx_scale (R : ringType) m n (a : R) :
  {morph @trmx _ m n : x / (a *: x)}%R.
Proof. by move => x; apply/matrixP => i j; rewrite !mxE. Qed.

Lemma row_permI (R : Type) (m n : nat) (p : 'S_m) :
  injective (@row_perm R m n p).
Proof.
by move => mx1 mx2 /(f_equal (row_perm p^-1));
   rewrite -!row_permM mulVg !row_perm1.
Qed.

Lemma col_permI (R : Type) (m n : nat) (p : 'S_n) :
  injective (@col_perm R m n p).
Proof.
by move => mx1 mx2 /(f_equal (col_perm p^-1));
   rewrite -!col_permM mulVg !col_perm1.
Qed.

Lemma mulmx_cast (R : ringType) m n n' p
      (mx1 : 'M[R]_(m, n)) (mx2 : 'M[R]_(n, p)) (H : n = n') :
  (castmx (erefl _, H) mx1 *m castmx (H, erefl _) mx2 = mx1 *m mx2)%R.
Proof.
have H0: {on predT, bijective (cast_ord H)}
  by exists (cast_ord (esym H)) => i _; rewrite (cast_ordK, cast_ordKV).
apply/matrixP => i j; rewrite !mxE (reindex _ H0) /=.
by apply eq_bigr => k _; rewrite !castmxE cast_ordK !cast_ord_id.
Qed.

Lemma mulmx_trl
      (R : comRingType) m n p (mx1 : 'M[R]_(n, m)) (mx2 : 'M[R]_(n, p)) :
  (mx1^T *m mx2 = (mx2^T *m mx1)^T)%R.
Proof. by rewrite trmx_mul trmxK. Qed.

Lemma mulmx_trr
      (R : comRingType) m n p (mx1 : 'M[R]_(m, n)) (mx2 : 'M[R]_(p, n)) :
  (mx1 *m mx2^T = (mx2 *m mx1^T)^T)%R.
Proof. by rewrite trmx_mul trmxK. Qed.

Lemma trmx_sum (R : ringType) m n (I : Type) (r : seq I) (P : I -> bool)
               (A_ : I -> 'M[R]_(m, n)) :
  (\sum_(i <- r | P i) A_ i)^T%R = (\sum_(i <- r | P i) (A_ i)^T)%R.
Proof.
apply (big_rec2 (fun x y => x^T = y)%R); first by rewrite trmx0.
by move => i B C H <-; rewrite trmxD.
Qed.

Lemma mulmx_row_col (R : ringType) m n p (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p))
                    (i : 'I_m) (j : 'I_p) :
  ((A *m B) i j = (row i A *m col j B) 0 0)%R.
Proof. by rewrite !mxE /=; apply/eq_bigr => k _; rewrite !mxE. Qed.

(* mxvec_index, vec_mx_index *)

Section vec_mx_index.

Variable (m n : nat).

Definition vec_mx_index (i : 'I_(m * n)) : 'I_m * 'I_n :=
  enum_val (cast_ord (esym (mxvec_cast m n)) i).

Lemma vec_mx_indexK i : prod_curry (mxvec_index (n:=n)) (vec_mx_index i) = i.
Proof.
case_eq (vec_mx_index i) => j k /=.
by rewrite /mxvec_index /vec_mx_index => <-; rewrite enum_valK cast_ordKV.
Qed.

Lemma mxvec_indexK i j : vec_mx_index (mxvec_index i j) = (i, j).
Proof. by rewrite /vec_mx_index /mxvec_index /= cast_ordK enum_rankK. Qed.

End vec_mx_index.

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

Lemma eqmx_le m n (mx1 mx2 : 'M_(m, n)) :
  mx1 == mx2 = (mx1 <=m mx2)%R && (mx2 <=m mx1)%R.
Proof.
apply/esym/andP; case: eqP.
- by move => ->; split; apply/lermxP => i j.
- move => H [] /lermxP H0 /lermxP H1; apply: H; apply/matrixP => i j; apply/eqP.
  by move: (H0 i j) (H1 i j); rewrite /= eqr_le => ->.
Qed.

Lemma lermx_opp2 m n : {mono -%R%R : x y /~ (x : 'M_(m, n)) <=m y}%R.
Proof.
move => mx1 mx2; apply/lermxP; case: lermxP.
- by move => H i j; move: (H i j); rewrite !mxE ler_opp2.
- by move => H H0; apply: H => i j; move: (H0 i j); rewrite !mxE ler_opp2.
Qed.

Lemma eq0mx_posmx m n (mx : 'M_(m, n)) :
  posmx mx && posmx (- mx)%R = (mx == 0%R).
Proof.
apply/andP; case: eqP.
- by move => ->; rewrite oppr0; split; apply/posmxP => i j; rewrite mxE.
- move => H [] /posmxP H0 /posmxP H1; apply: H; apply/matrixP => i j; apply/eqP.
  by move: (H0 i j) (H1 i j); rewrite !mxE oppr_ge0 eqr_le => -> ->.
Qed.

Lemma lermx_trmx m n (mx1 mx2 : 'M_(m, n)) :
  ((mx1^T <=m mx2^T) = (mx1 <=m mx2))%R.
Proof.
by apply/lermxP; case: lermxP;
  [move => H | move => H0 H; apply H0] => i j; move: (H j i); rewrite !mxE.
Qed.

Lemma posmx_trmx m n (mx : 'M_(m, n)) : posmx mx^T = posmx mx.
Proof. by rewrite /posmx -trmx0 lermx_trmx. Qed.

Lemma lermx_row_perm m n (p : 'S_m) (mx1 mx2 : 'M[R]_(m, n)) :
  (row_perm p mx1 <=m row_perm p mx2)%R = (mx1 <=m mx2)%R.
Proof.
by apply/lermxP; case: lermxP;
  [move => H i j; move: (H (p i) j) |
   move => H0 H; apply: H0 => i j; move: (H (p^-1 i) j)];
  rewrite !mxE ?permKV.
Qed.

Lemma lermx_col_perm m n (p : 'S_n) (mx1 mx2 : 'M[R]_(m, n)) :
  (col_perm p mx1 <=m col_perm p mx2)%R = (mx1 <=m mx2)%R.
Proof.
by rewrite -{1}(trmxK mx1) -{1}(trmxK mx2) -!tr_row_perm
           lermx_trmx lermx_row_perm lermx_trmx.
Qed.

Lemma posmx_row_perm m n (p : 'S_m) (mx : 'M[R]_(m, n)) :
  posmx (row_perm p mx) = posmx mx.
Proof.
rewrite /posmx -(lermx_row_perm p^-1) -row_permM mulVg row_perm1.
by congr lermx; apply/matrixP => i j; rewrite !mxE.
Qed.

Lemma posmx_col_perm m n (p : 'S_n) (mx : 'M[R]_(m, n)) :
  posmx (col_perm p mx) = posmx mx.
Proof.
by rewrite -{1}(trmxK mx) -tr_row_perm posmx_trmx posmx_row_perm posmx_trmx.
Qed.

Lemma lermx_castmx m n m' n' (H : (m = m') * (n = n')) (mx1 mx2 : 'M_(m, n)) :
  (castmx H mx1 <=m castmx H mx2)%R = (mx1 <=m mx2)%R.
Proof.
apply/lermxP; case: lermxP;
  [move => H0 | move => H1 H0; apply: H1]; move => i j.
- by rewrite !castmxE.
- by move: (H0 (cast_ord H.1 i) (cast_ord H.2 j)); rewrite !castmxE !cast_ordK.
Qed.

Lemma posmx_castmx m n m' n' (H : (m = m') * (n = n')) (mx : 'M_(m, n)) :
  posmx (castmx H mx) = posmx mx.
Proof.
rewrite /posmx.
have ->: (0 = castmx (R := R) H 0)%R
  by apply/matrixP => i j; rewrite castmxE !mxE.
by rewrite lermx_castmx.
Qed.

Lemma posmx_mul m n p (mx1 : 'M_(m, n)) (mx2 : 'M_(n, p)) :
  posmx mx1 -> posmx mx2 -> posmx (mx1 *m mx2).
Proof.
move => /posmxP H /posmxP H0; apply/posmxP => i j; rewrite !mxE /=.
by apply sumr_ge0 => k _; apply mulr_ge0.
Qed.

Lemma posmx_vec_mx m n (v : 'rV_(m * n)) : posmx (vec_mx v) = posmx v.
Proof.
apply/posmxP; case: posmxP; first by move => H i j; rewrite mxE.
move => H H0; apply: H => i j; case: {j} (mxvec_indexP j) => j k.
by move: (H0 j k); rewrite ord1 !mxE.
Qed.

Lemma posmx_mxvec m n (mx : 'M_(m, n)) : posmx (mxvec mx) = posmx mx.
Proof.
apply/posmxP; case: posmxP.
- by move => H i j; case: {j} (mxvec_indexP j) => j k; rewrite ord1 mxvecE.
- by move => H H0; apply: H => i j;
     move: (H0 0%R (mxvec_index i j)); rewrite mxvecE.
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

Lemma filter_mxE1' i j : filter_mx i j = A (enum_val i) j.
Proof. by rewrite !mxE. Qed.

Lemma filter_mxE2' (i : 'I_m) (j : 'I_n) (H : P (row i A)) :
  A i j = filter_mx (enum_rank_in H i) j.
Proof. by rewrite !mxE enum_rankK_in. Qed.

Lemma filter_mxT i : P (row i filter_mx).
Proof. by rewrite rowK; move: (enum_valP i). Qed.

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

Lemma subA0_0 i : (subA0 i 0 = 0)%R.
Proof. by move/eqP: (filter_mxT (A := A) (P := P0) i); rewrite /P0 !mxE. Qed.

Lemma subApos_pos i : (0 < subApos i 0)%R.
Proof. by move: (filter_mxT (A := A) (P := Ppos) i); rewrite /Ppos !mxE. Qed.

Lemma subAneg_neg i : (subAneg i 0 < 0)%R.
Proof. by move: (filter_mxT (A := A) (P := Pneg) i); rewrite /Pneg !mxE. Qed.

Definition nf := col_mx (col_mx subA0 subApos) subAneg.

Lemma rowsE : m = #|[pred i | P0 (row i A)]| +
                  #|[pred i | Ppos (row i A)]| +
                  #|[pred i | Pneg (row i A)]|.
Proof.
rewrite -cardUI.
have/eq_card0 ->:
    [predI [pred i | P0 (row i A)] & [pred i | Ppos (row i A)]] =i pred0
  by move => /= i; rewrite !inE /P0 /Ppos ltr_def andbA andbN.
have/eq_card ->:
    [predU [pred i | P0 (row i A)] & [pred i | Ppos (row i A)]] =i
    [pred i | 0 <= (row i A) 0 0]%R
  by move => /= i; rewrite !inE ler_eqVlt eq_sym.
rewrite addn0 -cardUI.
have/eq_card0 ->:
    [predI [pred i | 0 <= row i A 0 0]%R & [pred i | Pneg (row i A)]] =i pred0
  by move => /= i; rewrite !inE /Pneg ler_lt_asym.
have/eq_cardT ->:
    [predU [pred i | 0 <= row i A 0 0]%R & [pred i | Pneg (row i A)]] =i predT
  by move => /= i; rewrite !inE; case: (lerP 0 (row i A 0 0))%R.
by rewrite -cardE card_ord.
Qed.

Definition nf_perm_invf (i : 'I_m) : 'I_m :=
  cast_ord (esym rowsE)
  match ltrgt0P (row i A 0 0)%R with
  | ComparerEq0 H => lshift _ (lshift _ (enum_rank_in (introT eqP H) i))
  | ComparerGt0 H => lshift _ (rshift _ (enum_rank_in H i))
  | ComparerLt0 H => rshift _ (enum_rank_in H i)
  end.

Lemma nf_permI : injective nf_perm_invf.
Proof.
move => i j /cast_ord_inj.
by case (ltrgt0P (row i A 0 0)%R) => H; case (ltrgt0P (row j A 0 0)%R) => H0;
  do ?(move/lshift_inj || move/rshift_inj);
  move/enum_rank_in_inj || move/lshift_rshift_neq || move/rshift_lshift_neq.
Qed.

Definition nf_perm : 'S_m := (perm nf_permI)^-1.

Lemma nf_perm_eq : row_perm nf_perm A = castmx (esym rowsE, erefl) nf.
Proof.
apply row_permI with (perm nf_permI); rewrite -row_permM mulgV row_perm1.
apply/matrixP => i j;
  rewrite !mxE castmxE permE /= /nf_perm cast_ordK cast_ord_id.
by case (ltrgt0P (row i A 0 0)%R) => H /=;
  rewrite ?(col_mxEu, col_mxEd) !mxE enum_rankK_in // inE /P0 H.
Qed.

Check vec_mx_index.

Definition fm :
  'M[R]_(#|[pred i | P0 (row i A)]| +
         #|[pred i | Ppos (row i A)]| * #|[pred i | Pneg (row i A)]|, n) :=
  col_mx (rsubmx subA0)
         (\matrix_i' let: (i, j) := vec_mx_index i' in
                     subApos i 0 *: rsubmx (row j subAneg) -
                     subAneg j 0 *: rsubmx (row i subApos))%R.

Lemma fmP (x : 'cV[R]_n) :
  reflect (exists x0, posmx (A *m (col_mx (const_mx x0) x)))%R
          (posmx (fm *m x))%R.
Proof.
rewrite mul_col_mx posmx_col.
have ->: posmx (\matrix_i' (let: (i, j) := vec_mx_index i' in
                            subApos i 0%R *: rsubmx (row j subAneg) -
                            subAneg j 0%R *: rsubmx (row i subApos)) *m x) =
         [forall i, (subAneg i.2 0 * (rsubmx (row i.1 subApos) *m x) 0 0 <=
                     subApos i.1 0 * (rsubmx (row i.2 subAneg) *m x) 0 0)%R].
  apply/posmx_mulP; case: forallP => /=.
  - move => H i j; rewrite ord1 rowK {j};
      case: {i} (mxvec_indexP i) => i j; move: (H (i, j)) => //=.
    by rewrite mxvec_indexK col_id mulmxBl (mxE addmx_key) (mxE oppmx_key)
               subr_ge0 -!scalemxAl !(mxE scalemx_key) (H (i, j)).
  - move => H' H; apply: H' => -[i j] /=; move: {H} (H (mxvec_index i j) 0%R).
    by rewrite rowK mxvec_indexK col_id mulmxBl
               mxE (mxE oppmx_key) subr_ge0 -!scalemxAl !(mxE scalemx_key).
have H_A0E x0: posmx (rsubmx subA0 *m x) =
              posmx (subA0 *m col_mx (const_mx (m := 1) x0) x).
  congr posmx; apply/esym; rewrite -{1}(hsubmxK subA0) mul_row_col.
  suff ->: lsubmx subA0 = 0%R by rewrite mul0mx add0r.
  apply/esym/matrixP => i j; rewrite ord1 2!mxE -(subA0_0 i) {j}.
  by congr (subA0 _ _); apply/val_inj.
have {H_A0E} H_decomp_ineq x0:
  posmx (A *m col_mx (const_mx (m := 1) x0) x) =
  [&& posmx (rsubmx subA0 *m x),
      posmx (subApos *m col_mx (const_mx (m := 1) x0) x) &
      posmx (subAneg *m col_mx (const_mx (m := 1) x0) x)].
  rewrite (H_A0E x0); apply/posmx_mulP; case: and3P;
    last by move => H H0; apply: H; split;
            apply/posmx_mulP => i j; move: H0; rewrite filter_mxE1.
  by case => H H0 H1 i j; case: (ltrgt0P (row i A 0 0))%R;
    last move/eqP; move => H2;
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
              | inl i => `[b (row i subApos), +oo[
              | inr j => `]-oo, b (row j subAneg)]
            end)%R
    by rewrite /= itv_intersection_isnot0E;
      apply/all_allpairsP => -[] /= i [] j _ _ //=; first (by case: ifP);
      rewrite !mulNr ler_opp2 !(mxE matrix_key _ 0%R);
      [move: (H0 (i, j)) | move: (H0 (j, i))];
      rewrite /= !(mulrC _ (_ 0 0)%R) ler_pdivl_mulr ?subApos_pos //
              mulrAC ler_ndivr_mulr // ?subAneg_neg.
    rewrite /= big_sumType /=.
  case/itv_isnot0P => /= x0; rewrite itv_intersectionE -!itv_bigIE
    => /= /andP [] /allP /= H1 /allP /= H2; exists x0.
  apply/andP; split; apply/posmx_mulP => i j;
    rewrite ord1 {j} col_id -(hsubmxK (row i _)) mul_row_col 2!mxE big_ord1
            2!mxE (mxE const_mx_key) (val_inj _ _ _ : lshift n 0 = 0)%R //
            ?(addrC (subAneg _ _ * _)%R) -[X in (_ + X)%R]opprK subr_ge0
            -?mulNr mulrC.
  + rewrite -ler_pdivr_mulr ?subApos_pos //.
    by move: (H1 i); rewrite mem_index_enum inE andbT => /(_ erefl);
      congr (- _ / _ <= _)%R; rewrite !mxE.
  + rewrite -ler_pdivl_mulr ?oppr_gt0 ?subAneg_neg // invrN mulrN -mulNr.
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
  by rewrite -(ler_nmul2l (subAneg_neg j)) -(ler_pmul2l (subApos_pos i) (- _)%R)
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
    suff ->: const_mx (x 0 0)%R = usubmx (m1 := 1) x by rewrite vsubmxK.
    by apply/matrixP => i j; rewrite !mxE;
      congr (x _ _); apply/val_inj => /=; rewrite ord1.
Qed.

(* Farkas' lemma *)

Lemma Farkas_subproof_direct
      (R : realFieldType) m n (A : 'M[R]_(m, n)) (b : 'cV_m) :
  (exists x : 'cV_n, A *m x <=m b)%R ->
  (forall y : 'cV_m, posmx y -> A^T *m y = 0 -> posmx (y^T *m b))%R.
Proof.
case => x /lermxP H y /posmxP /= H0 H1;
  apply/posmxP => i j; rewrite !ord1 {i j}.
have ->: (0 = (y^T *m (A *m x)) 0 0)%R
  by rewrite mulmxA mulmx_trl H1 mulmx_trl mulmx0 !mxE.
rewrite -subr_ge0.
have <- : ((y^T *m (b - (A *m x))) 0 0 =
           (y^T *m b) 0 0 - (y^T *m (A *m x)) 0 0)%R
  by rewrite mulmxBr mxE (mxE oppmx_key).
by rewrite mxE /=; apply sumr_ge0 => i _; rewrite 3!mxE;
   apply mulr_ge0 => //; rewrite subr_ge0.
Qed.

Lemma Farkas_subproof_converse
      (R : realFieldType) m n (A : 'M[R]_(m, n)) (b : 'cV_m) :
  (forall y : 'cV_m, posmx y -> A^T *m y = 0 -> posmx (y^T *m b))%R ->
  (exists x : 'cV_n, A *m x <=m b)%R.
Proof.
move => H'.
suff [x /posmxP H0]: exists x : 'cV_n,
    posmx (row_mx A b *m (col_mx x (const_mx (n := 1) 1)))%R.
  by exists (- x)%R; apply/lermxP => i j; move: {H0} (H0 i j);
     rewrite ord1 mulmxN mul_row_col mxE addrC mxE /= big_ord1 mxE mulr1
             (mxE oppmx_key) -(subr_ge0 _ (b i 0%R)) opprK.
apply/Fourier_Motzkin_mP/negP; move/negP/Fourier_Motzkin_mP => H; move: H'.
suff [y]: exists2 y : 'rV_m,
    posmx y & (y *m (row_mx A b) = row_mx 0 (const_mx (-1)))%R
  by rewrite -(posmx_trmx y) mul_mx_row => H0 /eq_row_mx [H1 H2] /(_ y^T H0)%R;
     rewrite trmxK -trmx_mul H1 trmx0 H2 => /(_ erefl) /posmxP /(_ 0 0)%R;
     rewrite mxE ler0N1.
elim: n m {A b} (row_mx A b) H => //= [| n IHn] m A H.
- have {H} H: forall x : 'cV_0, ~ posmx (A *m col_mx x (const_mx 1%R))
    by move => x H0; apply H; exists x.
  move/negP: {H} (H 0%R);
    rewrite -{1}(hsubmxK A) mul_row_col mulmx0 add0r negb_forall.
  case/existsP => -[] /= i j;
    rewrite ord1 {j} !mxE /= big_ord1 !mxE mulr1 -ltrNge => H.
  have {H} H: (A i 0 < 0)%R by  move: H; congr (A _ _ < _)%R; apply/val_inj.
  exists ((- 1 / A i 0) *: delta_mx 0 i)%R.
  + apply/posmxP => k j; rewrite !ord1 {k} !mxE eqxx /=.
    apply mulr_ge0; last by case: (_ == _) => //=; rewrite mulr1n ler01.
    by apply mulr_le0; rewrite ?lerN10 // invr_le0; apply ltrW.
  + rewrite -scalemxAl -rowE; apply/matrixP => j k; rewrite !ord1 !mxE;
      case: splitP; first by case.
    by move => k' _; rewrite !ord1 !mxE -mulrA mulVf ?mulr1 // ltr0_neq0.
- suff [y H0 <-]: exists2 y : 'rV__,
                    posmx y & (y *m Fourier_Motzkin.nf A =
                               row_mx (n1 := n.+1) 0 (const_mx (-1)))%R
    by exists (col_perm (Fourier_Motzkin.nf_perm A)^-1
                        (castmx (erefl, esym (Fourier_Motzkin.rowsE A)) y));
      [rewrite posmx_col_perm posmx_castmx |
       rewrite mul_col_perm invgK Fourier_Motzkin.nf_perm_eq mulmx_cast].
  have {IHn} /IHn [y H0]:
    ~(exists x : 'cV_n, posmx ((Fourier_Motzkin A) *m col_mx x (const_mx 1%R))).
    case => x0 /Fourier_MotzkinP [x H0]; apply H.
    exists (col_mx (const_mx (m := 1) x) x0); move: H0.
    congr (posmx (_ *m _)); apply/matrixP => i j.
    by rewrite col_mxA castmxE /=; congr (col_mx _ _ _ _); apply/val_inj.
  rewrite /Fourier_Motzkin /Fourier_Motzkin.fm /Fourier_Motzkin.nf.
  set subA0 := Fourier_Motzkin.subA0 A.
  set subApos := Fourier_Motzkin.subApos A.
  set subAneg := Fourier_Motzkin.subAneg A.
  set subApn := (\matrix_i' _)%R.
  rewrite -(hsubmxK y) mul_row_col => H1.
  exists (row_mx (row_mx (lsubmx y)
                         (((- col 0 subAneg)^T *m (vec_mx (rsubmx y))^T)))
                 ((col 0 subApos)^T *m vec_mx (rsubmx y)))%R.
    move: H0; rewrite -{1}(hsubmxK y) posmx_row => /andP [H0 H0'];
      rewrite !posmx_row H0 /=; apply/andP; split; apply posmx_mul;
      rewrite ?posmx_trmx ?posmx_vec_mx //; apply/posmxP => i j;
      rewrite ?(mxE oppmx_key) mxE ?oppr_ge0; apply ltrW;
        [apply Fourier_Motzkin.subAneg_neg | apply Fourier_Motzkin.subApos_pos].
  have ->: row_mx (R := R) (n1 := n.+1) (m := 1) 0 (const_mx (-1)%R) =
           row_mx (n1 := 1) (n2 := n + 1) 0 (row_mx 0 (const_mx (-1)%R))
    by apply/matrixP => i j; rewrite row_mxA castmxE; congr (row_mx _ _ _ _);
      rewrite ?row_mx0 //; apply/val_inj.
  rewrite -{}H1 !mul_row_col -(hsubmxK (_ + _ + _)%R);
    congr row_mx; apply/matrixP => i j.
  + rewrite !ord1 3!mxE {i j} lshift0 mulmx_row_col.
    have ->: col 0%R subA0 = 0%R
      by apply/matrixP => i j; rewrite mxE Fourier_Motzkin.subA0_0 mxE.
    by rewrite mulmx0 mxE add0r mulmx_row_col row_id -trmx_mul mulmx_trl
               mulmxA mulmxN 2!mxE addrC mulmx_row_col row_id subrr.
  + rewrite (mxE rsubmx_key) !(mxE addmx_key) !(mulmx_row_col (lsubmx y)) -addrA;
      congr ((_ *m _) _ _ + _)%R; first by apply/matrixP => k l; rewrite !mxE.
    rewrite !(mulmx_row_col _ _ i (rshift 1 j)) !row_id -trmx_mul mulmx_trl
            mxE mulmxA mulmxN addrC -(trmxK (col _ subAneg))
            -(trmxK (col 0%R subAneg)) -!mxvec_dotmul !trmxK vec_mxK.
    have ->: forall (mx1 mx2 : 'M[R]_1), (mx1 0 0 + mx2 0 0 = (mx1 + mx2) 0 0)%R
      by move => mx1 mx2; rewrite !mxE.
    rewrite -mulmxBl mulmx_trr mxE (mulmx_row_col _ _ i j) row_id.
    by congr ((_ *m _) _ _)%R; apply/matrixP => k l; rewrite !ord1 {i l} !mxE;
      case: {k} (mxvec_indexP k) => k l;
      rewrite !mxvecE mxvec_indexK !mxE !big_ord1 !mxE (mulrC _ (A _ 0%R)).
Qed.

Lemma Farkas_subproof
      (R : realFieldType) m n (A : 'M[R]_(m, n)) (b : 'cV_m) :
  (forall y : 'cV_m, posmx y -> A^T *m y = 0 -> posmx (y^T *m b))%R <->
  (exists x : 'cV_n, A *m x <=m b)%R.
Proof.
split.
- apply Farkas_subproof_converse.
- apply Farkas_subproof_direct.
Qed.

Lemma Farkas (R : realFieldType) m n (A : 'M[R]_(m, n)) (b : 'cV_m) :
  (forall y : 'cV_m, posmx (y^T *m A) -> posmx (y^T *m b))%R <->
  (exists2 x : 'cV_n, posmx x & A *m x = b)%R.
Proof.
split; last by move => [x H] <- {b} y H0; rewrite mulmxA; apply posmx_mul.
move => H.
suff [x]: exists x : 'cV_n,
  (col_mx (col_mx A (- A)) (- 1%:M) *m x <=m col_mx (col_mx b (-b)) 0)%R
  by rewrite !mul_col_mx !lermx_col !mulNmx mul1mx lermx_opp2 -eqmx_le
             -lermx_opp2 oppr0 opprK => /andP [/eqP <- H0]; exists x.
apply Farkas_subproof_converse => y.
rewrite -(vsubmxK y) -(vsubmxK (usubmx y)) !posmx_col !tr_col_mx !mul_row_col.
move: (usubmx (usubmx y)) (dsubmx (usubmx y)) (dsubmx y) => u v w.
by rewrite -andbA !trmxN !mulNmx trmx1 mul1mx mulmx0 addr0
  => /and3P [H0 H1 H2] /eqP; rewrite subr_eq0 => /eqP H3; subst w; move: H2;
  rewrite mulmxN -mulmxBl -mulmxBr -trmxN -trmxD mulmx_trl posmx_trmx => /H.
Qed.
