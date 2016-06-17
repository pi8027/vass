Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp.
Import GroupScope GRing.Theory Num.Theory.
Require Import utils.

(******************************************************************************)
(*  Linear rational arithmetic and Fourier-Motzkin variable elimination       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LRA_term.

Variable (dim : nat).

Inductive LRA_term :=
  | LRA_zero
  | LRA_var  of 'I_dim
  | LRA_add  of LRA_term & LRA_term.

Fixpoint eq_LRA_term (t1 t2 : LRA_term) :=
  match t1, t2 with
    | LRA_zero, LRA_zero => true
    | LRA_var x, LRA_var y => x == y
    | LRA_add t1l t1r, LRA_add t2l t2r =>
      eq_LRA_term t1l t2l && eq_LRA_term t1r t2r
    | _, _ => false
  end.

Lemma eq_LRA_termP : Equality.axiom eq_LRA_term.
Proof.
move => t1 t2; apply: (iffP idP) => [| <-].
- by elim: t1 t2 => [| x | t1l IHl t1r IHr]
                    [| //= y /eqP -> | //= t2l t2r /andP [] /IHl -> /IHr ->].
- by elim: t1 => //= t1l ->.
Defined.

Canonical LRA_term_eqMixin := EqMixin eq_LRA_termP.
Canonical LRA_term_eqType := Eval hnf in EqType LRA_term LRA_term_eqMixin.

Inductive QFLRA_formula :=
  | QFLRA_neg   of QFLRA_formula
  | QFLRA_and   of QFLRA_formula & QFLRA_formula
  | QFLRA_or    of QFLRA_formula & QFLRA_formula
  | QFLRA_imply of QFLRA_formula & QFLRA_formula
  | QFLRA_leq   of 'cV[rat]_dim.

Fixpoint eq_QFLRA_formula (f1 f2 : QFLRA_formula) :=
  match f1, f2 with
    | QFLRA_neg f1', QFLRA_neg f2' => eq_QFLRA_formula f1' f2'
    | QFLRA_and f1l f1r, QFLRA_and f2l f2r =>
      eq_QFLRA_formula f1l f2l && eq_QFLRA_formula f1r f2r
    | QFLRA_or f1l f1r, QFLRA_or f2l f2r =>
      eq_QFLRA_formula f1l f2l && eq_QFLRA_formula f1r f2r
    | QFLRA_imply f1l f1r, QFLRA_imply f2l f2r =>
      eq_QFLRA_formula f1l f2l && eq_QFLRA_formula f1r f2r
    | QFLRA_leq t1, QFLRA_leq t2 => t1 == t2
    | _, _ => false
  end.

Lemma eq_QFLRA_formulaP : Equality.axiom eq_QFLRA_formula.
Proof.
move => f1 f2; apply: (iffP idP) => [| <-].
- by elim: f1 f2 =>
    [f1' IH | f1l IHl f1r IHr | f1l IHl f1r IHr | f1l IHl f1r IHr | t1]
    [//= f2' /IH -> | | | | //= t2 /eqP ->]
    //= f2l f2r /andP [] /IHl -> /IHr ->.
- by elim: f1 => //= [f1l -> | f1l -> | f1l ->] *; rewrite ?eqxx.
Defined.

Canonical QFLRA_formula_eqMixin := EqMixin eq_QFLRA_formulaP.
Canonical QFLRA_formula_eqType :=
  Eval hnf in EqType QFLRA_formula QFLRA_formula_eqMixin.

End LRA_term.

Inductive LRA_formula (dim : nat) :=
  | LRA_forall  of LRA_formula (1 + dim)
  | LRA_exists  of LRA_formula (1 + dim)
  | LRA_neg     of LRA_formula dim
  | LRA_and     of LRA_formula dim & LRA_formula dim
  | LRA_or      of LRA_formula dim & LRA_formula dim
  | LRA_imply   of LRA_formula dim & LRA_formula dim
  | LRA_leq     of LRA_term dim & LRA_term dim.

Definition LRA_literal dim := [eqType of bool * 'cV[rat]_dim].
(*
b, (c_1, ..., c_d) =>
  {(x_1, ..., x_d) | 0 # x_1 c_1 + ... + x_d c_d
                   | (#) = if b then (<) else (<=) }
*)

Definition LRA_interpret_af dim (I f : 'cV[rat]_dim) := ((f^T *m I) 0 0)%R.

Definition LRA_interpret_literal dim (I : 'cV_dim) (f : LRA_literal dim) :=
  lter f.1 0%R (LRA_interpret_af I f.2).

Lemma LRA_af_recl dim (I f : 'cV_(1 + dim)) :
  LRA_interpret_af I f =
  (f 0 0 * I 0 0 + LRA_interpret_af (dsubmx I) (dsubmx f))%R.
Proof.
by rewrite /LRA_interpret_af -{1}(hsubmxK f^T) -{1}(vsubmxK I) mul_row_col
           2!mxE big_ord_recl big_ord0 3!mxE addr0 lshift0 trmx_dsub.
Qed.

Fixpoint LRA_term_val dim (I : 'cV_dim) (t : LRA_term dim) : rat :=
  match t with
    | LRA_zero => 0%R
    | LRA_var i => I i 0%R
    | LRA_add t1 t2 => (LRA_term_val I t1 + LRA_term_val I t2)%R
  end.

Fixpoint LRA_af_of_term dim (t : LRA_term dim) (i : 'I_dim) : nat :=
  match t with
  | LRA_zero => 0
  | LRA_var i' => i == i'
  | LRA_add t1 t2 => LRA_af_of_term t1 i + LRA_af_of_term t2 i
  end.

Lemma LRA_interpret_af_add dim (I f1 f2 : 'cV_dim) :
  (LRA_interpret_af I (f1 + f2) =
   LRA_interpret_af I f1 + LRA_interpret_af I f2)%R.
Proof.
by rewrite /LRA_interpret_af !mxE -big_split /=;
  apply/eq_bigr => i _; rewrite !mxE mulrDl.
Qed.

Lemma LRA_interpret_af_opp dim (I f : 'cV_dim) :
  (LRA_interpret_af I (- f) = - LRA_interpret_af I f)%R.
Proof.
by rewrite /LRA_interpret_af !mxE (big_endo _ (@opprD _)) //;
  apply/eq_bigr => /= i _; rewrite !mxE mulNr.
Qed.

Lemma LRA_term_val_af dim (I : 'cV_dim) (t : LRA_term dim) :
  LRA_term_val I t = (\sum_(i < dim) I i 0 *+ LRA_af_of_term t i)%R.
Proof.
elim: t => /=.
- by apply big_rec => //= i x _ <-; rewrite add0r.
- move => i.
  rewrite (bigID (pred1 i)) /= big_pred1_eq eqxx /=
          mulr1n -{1}(addr0 (I i 0))%R; congr +%R.
  by apply big_rec => //= j x /negPf -> <- /=; rewrite add0r.
- move => t1 -> t2 ->.
  by rewrite -big_split //=; apply eq_bigr => i _; rewrite mulrnDr.
Qed.

Fixpoint LRA_interpret_formula' dim (f : LRA_formula dim) : 'cV_dim -> Prop :=
  match f with
  | LRA_forall f' => fun I =>
    forall x, LRA_interpret_formula' f' (col_mx (const_mx x) I)
  | LRA_exists f' => fun I =>
    exists x, LRA_interpret_formula' f' (col_mx (const_mx x) I)
  | LRA_neg f' => fun I => ~ LRA_interpret_formula' f' I
  | LRA_and f1 f2 => fun I =>
    LRA_interpret_formula' f1 I /\ LRA_interpret_formula' f2 I
  | LRA_or f1 f2 => fun I =>
    LRA_interpret_formula' f1 I \/ LRA_interpret_formula' f2 I
  | LRA_imply f1 f2 => fun I =>
    LRA_interpret_formula' f1 I -> LRA_interpret_formula' f2 I
  | LRA_leq t1 t2 => fun I => (LRA_term_val I t1 <= LRA_term_val I t2)%R
  end.

Notation LRA_interpret_formula I f := (@LRA_interpret_formula' _ f I).

Fixpoint QFLRA_interpret_formula
  dim (I : 'cV_dim) (f : QFLRA_formula dim) : bool :=
  match f with
    | QFLRA_neg f       => ~~ QFLRA_interpret_formula I f
    | QFLRA_and f1 f2   => QFLRA_interpret_formula I f1 &&
                           QFLRA_interpret_formula I f2
    | QFLRA_or f1 f2    => QFLRA_interpret_formula I f1 ||
                           QFLRA_interpret_formula I f2
    | QFLRA_imply f1 f2 => QFLRA_interpret_formula I f1 ==>
                           QFLRA_interpret_formula I f2
    | QFLRA_leq t       => (0 <= (t^T *m I) 0 0)%R
  end.

Definition QFLRA_top dim : QFLRA_formula dim := QFLRA_leq 0%R.
Arguments QFLRA_top {dim}.

Lemma QFLRA_top_true dim (I : 'cV_dim) : QFLRA_interpret_formula I QFLRA_top.
Proof. by rewrite /= mxE; apply sumr_ge0 => i _; rewrite !mxE mul0r. Qed.

Definition QFLRA_bot dim : QFLRA_formula dim := QFLRA_neg QFLRA_top.
Arguments QFLRA_bot {dim}.

Lemma QFLRA_bot_false dim (I : 'cV_dim) :
  QFLRA_interpret_formula I QFLRA_bot = false.
Proof. by move: (QFLRA_top_true I) => /= ->. Qed.

Definition NF_neg dim (fss : seq (seq (LRA_literal dim))) :=
  [seq [seq (negb f.1, - f.2)%R | f : LRA_literal dim <- fs] |
   fs <- fss].

Lemma NF_neg_CNF dim (I : 'cV_dim) lss :
  has (all (LRA_interpret_literal I)) (NF_neg lss) =
  ~~ all (has (LRA_interpret_literal I)) lss.
Proof.
rewrite /NF_neg /LRA_interpret_literal -has_predC has_map.
apply eq_in_has => /= afs _; rewrite -all_predC all_map.
apply eq_in_all => -[f t] _ /=; rewrite lterN -lter_opp2 oppr0.
congr lter; rewrite /LRA_interpret_af !mxE big_endo //; last apply opprD.
by apply eq_bigr => i _; rewrite !mxE mulNr opprK.
Qed.

Lemma NF_neg_DNF dim (I : 'cV_dim) lss :
  all (has (LRA_interpret_literal I)) (NF_neg lss) =
  ~~ has (all (LRA_interpret_literal I)) lss.
Proof.
rewrite /NF_neg /LRA_interpret_literal -all_predC all_map.
apply eq_in_all => /= afs _; rewrite -has_predC has_map.
apply eq_in_has => -[f t] _ /=; rewrite lterN -lter_opp2 oppr0.
congr lter; rewrite /LRA_interpret_af !mxE big_endo //; last apply opprD.
by apply eq_bigr => i _; rewrite !mxE mulNr opprK.
Qed.

Fixpoint
  QFLRA_DNF dim (f : QFLRA_formula dim) : seq (seq (LRA_literal dim)) :=
  match f with
    | QFLRA_neg f' => NF_neg (QFLRA_CNF f')
    | QFLRA_and f1 f2 =>
      [seq fs1 ++ fs2 | fs1 <- QFLRA_DNF f1, fs2 <- QFLRA_DNF f2]
    | QFLRA_or f1 f2 => QFLRA_DNF f1 ++ QFLRA_DNF f2
    | QFLRA_imply f1 f2 => NF_neg (QFLRA_CNF f1) ++ QFLRA_DNF f2
    | QFLRA_leq f' => [:: [:: (true, f')]]
  end with
  QFLRA_CNF dim (f : QFLRA_formula dim) : seq (seq (LRA_literal dim)) :=
  match f with
    | QFLRA_neg f' => NF_neg (QFLRA_DNF f')
    | QFLRA_and f1 f2 => QFLRA_CNF f1 ++ QFLRA_CNF f2
    | QFLRA_or f1 f2 =>
      [seq fs1 ++ fs2 | fs1 <- QFLRA_CNF f1, fs2 <- QFLRA_CNF f2]
    | QFLRA_imply f1 f2 =>
      [seq fs1 ++ fs2 | fs1 <- NF_neg (QFLRA_DNF f1), fs2 <- QFLRA_CNF f2]
    | QFLRA_leq f' => [:: [:: (true, f')]]
  end.

Lemma QFLRA_NF_correctness dim (I : 'cV_dim) (f : QFLRA_formula dim) :
  (has (all (LRA_interpret_literal I)) (QFLRA_DNF f) =
     QFLRA_interpret_formula I f) *
  (all (has (LRA_interpret_literal I)) (QFLRA_CNF f) =
     QFLRA_interpret_formula I f).
Proof.
move: f; refine (@QFLRA_formula_ind dim _ _ _ _ _ _) => /=.
- by move => q [] {3}<- <-; rewrite NF_neg_CNF NF_neg_DNF.
- move => q1 [] {2}<- <- q2 [] {2}<- <-; split; last by rewrite all_cat.
  elim: (QFLRA_DNF q1) => //= qs qss IH.
  rewrite has_cat {}IH andb_orl; congr orb.
  elim: (QFLRA_DNF q2); rewrite /= ?andbF => // qs' qss' IH.
  by rewrite all_cat {}IH andb_orr.
- move => q1 [] {2}<- <- q2 [] {2}<- <-; split; first by rewrite has_cat.
  elim: (QFLRA_CNF q1) => //= qs qss IH.
  rewrite all_cat {}IH orb_andl; congr andb.
  elim: (QFLRA_CNF q2); rewrite /= ?orbT => // qs' qss' IH.
  by rewrite has_cat {}IH orb_andr.
- move => q1 [] {3}<- <- q2 [] {2}<- <-;
  rewrite !implybE has_cat NF_neg_CNF -NF_neg_DNF; split => //.
  elim: (NF_neg _) => //= qs qss IH.
  rewrite all_cat {}IH orb_andl; congr andb.
  elim: (QFLRA_CNF q2); rewrite /= ?orbT => // qs' qss' IH.
  by rewrite has_cat {}IH orb_andr.
- by move => f; rewrite !andbT !orbF /=.
Qed.

Lemma QFLRA_DNF_correctness dim (I : 'cV_dim) (f : QFLRA_formula dim) :
  has (all (LRA_interpret_literal I)) (QFLRA_DNF f) =
  QFLRA_interpret_formula I f.
Proof. by case: (QFLRA_NF_correctness I f). Qed.

Lemma QFLRA_CNF_correctness dim (I : 'cV_dim) (f : QFLRA_formula dim) :
  all (has (LRA_interpret_literal I)) (QFLRA_CNF f) =
  QFLRA_interpret_formula I f.
Proof. by case: (QFLRA_NF_correctness I f). Qed.

Definition QFLRA_l2f dim (l : LRA_literal dim) :=
  if l.1 then QFLRA_leq l.2 else QFLRA_neg (QFLRA_leq (- l.2)%R).

Lemma QFLRA_l2f_correctness dim (I : 'cV_dim) (l : LRA_literal dim) :
  LRA_interpret_literal I l = QFLRA_interpret_formula I (QFLRA_l2f l).
Proof.
rewrite /QFLRA_l2f /LRA_interpret_literal; case: l.1 => //=.
rewrite -ltrNge -subr_lt0 sub0r; congr (_ < _)%R.
rewrite /LRA_interpret_af !mxE big_endo //; last apply opprD.
by apply eq_bigr => i _; rewrite !mxE mulNr.
Qed.

Definition QFLRA_unDNF dim (lss : seq (seq (LRA_literal dim))) :=
  foldr (fun ls => QFLRA_or
                     (foldr (fun l => QFLRA_and (QFLRA_l2f l)) QFLRA_top ls))
        QFLRA_bot lss.

Lemma QFLRA_unDNF_correctness
  dim (I : 'cV_dim) (lss : seq (seq (LRA_literal dim))) :
  has (all (LRA_interpret_literal I)) lss =
  QFLRA_interpret_formula I (QFLRA_unDNF lss).
Proof.
elim: lss; first by rewrite /foldr QFLRA_bot_false.
move => /= ls lss ->; congr orb.
elim: ls {lss}; first by rewrite /foldr QFLRA_top_true.
move => /= l ls ->; congr andb; apply QFLRA_l2f_correctness.
Qed.

Definition exists_conj_elim
  dim (ls : seq (LRA_literal (1 + dim))) : seq (LRA_literal dim) :=
  let lsp := [seq l : LRA_literal (1 + dim) <- ls | (0 < l.2 0 0)]%R in
    (* - (a_1 x_1 + ... + a_n x_n) <<= a_0 x_0 *)
  let lsn := [seq l : LRA_literal (1 + dim) <- ls | (0 > l.2 0 0)]%R in
    (* - b_0 x_0 <<= b_1 x_1 + ... + b_n x_n *)
  [seq (l.1, dsubmx l.2)
    | l : LRA_literal (1 + dim) <- ls & l.2 0 0 == 0]%R ++
  [seq (lp.1 && ln.1, lp.2 0 0 *: dsubmx ln.2 -
                      ln.2 0 0 *: dsubmx lp.2)%R
    | lp : LRA_literal (1 + dim) <- lsp, ln : LRA_literal (1 + dim) <- lsn]
  (*
       - (a_1 x_1 + ... + a_n x_n) <<= a_0 x_0 /\
       - b_0 x_0 <<= b_1 x_1 + ... + b_n x_n
  <=>  b_0 (a_1 x_1 + ... + a_n x_n) <<= a_0 (b_1 x_1 + ... + b_n x_n)
  <=>  0 <= (a_0 b_1 - b_0 a_1) x_1 + ... + (a_0 b_n - b_0 a_n) x_n
  *).

Definition literal_interval dim (I : 'cV_dim) (l : LRA_literal (1 + dim)) :=
  let r := (- LRA_interpret_af I (dsubmx l.2) / l.2 0 0)%R in
  if (l.2 0 0 == 0)%R
  then if LRA_interpret_literal I (l.1, dsubmx l.2) then itv1 else itv0
  else if (0 < l.2 0 0)%R then Interval (BOpen_if (~~ l.1) r) (BInfty _)
                           else Interval (BInfty _) (BOpen_if (~~ l.1) r).

Lemma literal_intervalE dim x0 (I : 'cV_dim) (l : LRA_literal (1 + dim)) :
  LRA_interpret_literal (col_mx (const_mx x0) I) l =
  (x0 \in literal_interval I l).
Proof.
rewrite /literal_interval /LRA_interpret_literal LRA_af_recl
        /LRA_interpret_af trmx_dsub mxE split1 unlift_none /= mxE col_mxKd.
case: (ltrgtP (l.2 0 0) 0)%R => /= H;
  try by rewrite inE /= ?andbT addrC -lternE negbK addr_lte0r
                 (lter_ndivl_mulr, lter_pdivr_mulr) // mulrC.
by rewrite H mul0r add0r; case: (lter l.1 _ _); rewrite ?(itv1E, itv0E).
Qed.

Lemma exists_conj_elimP dim I (ls : seq (LRA_literal (1 + dim))) :
  reflect
    (exists x, all (LRA_interpret_literal (col_mx (const_mx x) I)) ls)
    (all (LRA_interpret_literal I) (exists_conj_elim ls)).
Proof.
have af_decomp (l1 l2 : LRA_literal (1 + dim)) :
  LRA_interpret_af I
    (l1.2 0 0 *: dsubmx l2.2 - l2.2 0 0 *: dsubmx l1.2)%R =
  (l1.2 0 0 * LRA_interpret_af I (dsubmx l2.2) -
   l2.2 0 0 * LRA_interpret_af I (dsubmx l1.2))%R.
  rewrite /LRA_interpret_af !mxE.
  rewrite 2?big_endo ?mulr0 //; try by move => a b; rewrite mulrDr.
  rewrite big_endo //; last apply opprD.
  rewrite -big_split /=; apply eq_bigr => i _.
  by rewrite !mulrA -mulNr -mulrDl !mxE.
apply (iffP idP); rewrite /exists_conj_elim all_cat.
- case/andP; rewrite all_map => H /all_allpairsP H0.
  suff: itv_isnot0
          (\big[itv_intersection/itv1]_(l <- ls) literal_interval I l)
    by case/itv_isnot0P => /= x; rewrite -itv_bigIE => H1; exists x;
      apply/allP => /= l /(allP H1); rewrite literal_intervalE.
  have H1 (l : LRA_literal dim.+1) :
    (l.2 0 0 == 0)%R -> l \in ls -> literal_interval I l = itv1
    by move => H1 H2; rewrite /literal_interval H1;
       move: (allP H l); rewrite mem_filter H1 H2 /= => /(_ isT) ->.
  rewrite itv_intersection_isnot0E;
    apply/allP => /= itv /allpairsP [] [] /= l1 l2 [H2 H3 H4]; subst itv.
  case_eq (l1.2 0 0 == 0)%R => H4;
    first rewrite (H1 l1) // itv_intersection1i {H4};
    (case_eq (l2.2 0 0 == 0)%R => H5;
     first rewrite (H1 l2) // ?itv_intersectioni1 {H5});
    rewrite /literal_interval ?H4 ?H5;
    do !case: ifP => //=; move => H6 H7; try rewrite -negb_and negbK.
  + have {H4 H5 H6} H4: (l2.2 0 0 < 0)%R
      by rewrite ltrNge ler_eqVlt eq_sym H5 H6.
    move: (H0 l1 l2).
    by rewrite !mem_filter H2 H3 H4 H7 /LRA_interpret_literal /=
               lter_pdivr_mulr // mulrAC lter_ndivl_mulr // !mulNr
               -addr_lte0r af_decomp !(mulrC (LRA_interpret_af _ _))%R => ->.
  + have {H4 H5 H7} H4: (l1.2 0 0 < 0)%R
      by rewrite ltrNge ler_eqVlt eq_sym H4 H7.
    move: (H0 l2 l1).
    by rewrite !mem_filter H2 H3 H4 H6 /LRA_interpret_literal /=
               lter_pdivr_mulr // mulrAC lter_ndivl_mulr // !mulNr
               -addr_lte0r af_decomp !(mulrC (LRA_interpret_af _ _))%R => ->.
- case => x H; apply/andP; split.
  + rewrite all_map; apply/allP => /= l; rewrite mem_filter =>
      /andP [/eqP H0 /(allP H)].
    by rewrite /LRA_interpret_literal LRA_af_recl !mxE;
      case: splitP => i // _; rewrite ord1 H0 mul0r add0r col_mxKd.
  + apply/allP => l /allpairsP [] [] /= l1 l2 /= [].
    rewrite !mem_filter => //= /andP [H0] /(allP H) H1
                               /andP [H2] /(allP H) H3 ->.
    move: H0 H2 H1 H3.
    rewrite /LRA_interpret_literal /= !LRA_af_recl !mxE;
      case: splitP => i // _; rewrite ord1 !addr_lte0r af_decomp subr_lte0r.
    move => /(lter_pmul2l l2.1) <- /(lter_nmul2l l1.1) <-.
    rewrite !mulrN mulrCA col_mxKd !mxE; apply lter_trans.
Qed.

Definition exists_DNF_elim dim (lss : seq (seq (LRA_literal dim.+1))) :
  QFLRA_formula dim :=
  QFLRA_unDNF [seq exists_conj_elim ls | ls <- lss].

Lemma exists_DNF_elimP dim I (lss : seq (seq (LRA_literal (1 + dim)))) :
  reflect (exists x,
             has (all (LRA_interpret_literal (col_mx (const_mx x) I))) lss)
          (QFLRA_interpret_formula I (exists_DNF_elim lss)).
Proof.
rewrite /exists_DNF_elim -QFLRA_unDNF_correctness.
apply (iffP hasP).
- case => /= ls' /mapP [] /= ls H -> {ls'} /exists_conj_elimP [] x H0.
  by exists x; apply/hasP => /=; exists ls.
- case => x /hasP [] /= ls H H0; exists (exists_conj_elim ls).
  + by apply map_f.
  + by apply/exists_conj_elimP; exists x.
Qed.

Fixpoint Fourier_Motzkin dim (f : LRA_formula dim) : QFLRA_formula dim :=
  match f with
    | LRA_forall f' =>
      QFLRA_neg (exists_DNF_elim (QFLRA_DNF (QFLRA_neg (Fourier_Motzkin f'))))
    | LRA_exists f' =>
      exists_DNF_elim (QFLRA_DNF (Fourier_Motzkin f'))
    | LRA_neg f' => QFLRA_neg (Fourier_Motzkin f')
    | LRA_and f1 f2 => QFLRA_and (Fourier_Motzkin f1) (Fourier_Motzkin f2)
    | LRA_or f1 f2 => QFLRA_or (Fourier_Motzkin f1) (Fourier_Motzkin f2)
    | LRA_imply f1 f2 => QFLRA_imply (Fourier_Motzkin f1) (Fourier_Motzkin f2)
    | LRA_leq t1 t2 =>
      QFLRA_leq
        (\col_i ((LRA_af_of_term t2 i)%:Z - (LRA_af_of_term t1 i)%:Z)%:Q)%R
  end.

Lemma Fourier_MotzkinP dim I (f : LRA_formula dim) :
  reflect (LRA_interpret_formula I f)
          (QFLRA_interpret_formula I (Fourier_Motzkin f)).
Proof.
move: dim f I.
refine (LRA_formula_rect _ _ _ _ _ _ _) => //= dim.
- move => f IH I; apply/(iffP idP).
  + move/exists_DNF_elimP => H x; apply/IH.
    apply/negP => /negP H0; apply: H; exists x.
    by rewrite NF_neg_CNF QFLRA_NF_correctness.
  + move => H; apply/negP => /exists_DNF_elimP [x].
    by rewrite NF_neg_CNF QFLRA_NF_correctness => /IH; apply; apply H.
- move => f IH l; apply/(iffP idP).
  + by case/exists_DNF_elimP => x;
      rewrite QFLRA_NF_correctness => /IH H; exists x.
  + by move => [x H]; apply/exists_DNF_elimP;
      exists x; rewrite QFLRA_NF_correctness; apply/IH.
- by move => f IH I; apply/(iffP idP); move/IH.
- by move => f1 IH1 f2 IH2 I; apply/(iffP andP); case => /IH1 H /IH2 H0.
- by move => f1 IH1 f2 IH2 I; apply/(iffP orP);
    (case; [move/IH1; left | move/IH2; right]).
- by move => f1 IH1 f2 IH2 I; apply(iffP implyP) => H /IH1 /H /IH2.
- move => l1 l2 I; rewrite !LRA_term_val_af -subr_ge0 !mxE.
  set r1 := (_ - _)%R. set r2 := (\sum_i _)%R.
  suff ->: r1 = r2 by apply idP.
  subst r1 r2.
  rewrite (big_morph _ (@opprD _) erefl) -big_split /=.
  apply eq_bigr => /= i _; rewrite !mxE.
  by rewrite -(mul1r (_ *+ _ l1 _)%R) -(mul1r (_ *+ _ l2 _)%R)
             !mulrnAr (mulrC 1%R) -!mulrnAr -mulrBr mulrC /= mulrzBl_nat.
Qed.
