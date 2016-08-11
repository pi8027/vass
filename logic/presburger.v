From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp.
Require Import utils algebra_ext bigop_ext matrix_ext.
Import GroupScope GRing.Theory Num.Theory.

(******************************************************************************)
(*  Semilinear set and Presburger arithmetic                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Presburger formula and its interpretation *)

Inductive LIA_formula (dim : nat) :=
  | f_all     of LIA_formula (1 + dim)
  | f_exists  of LIA_formula (1 + dim)
  | f_neg     of LIA_formula dim
  | f_and     of LIA_formula dim & LIA_formula dim
  | f_or      of LIA_formula dim & LIA_formula dim
  | f_leq     of 'cV[int]_dim & int.

Fixpoint interpret_formula dim (f : LIA_formula dim) : 'cV[int]_dim -> Prop :=
  match f with
    | f_all f => fun I => forall n, interpret_formula f (col_mx (const_mx n) I)
    | f_exists f =>
      fun I => exists n, interpret_formula f (col_mx (const_mx n) I)
    | f_neg f => fun I => ~ interpret_formula f I
    | f_and f f' => fun I => interpret_formula f I /\ interpret_formula f' I
    | f_or f f' => fun I => interpret_formula f I \/ interpret_formula f' I
    | f_leq t n => fun I => (0 <= n + (t^T *m I) 0 0)%R
  end.

(* Quantifier free Presburger formula and negation free normal forms *)

Section QFLIA.

Variable (dim : nat).

Inductive QFLIA_af :=
  | QFLIA_leq       of int & 'cV[int]_dim
  | QFLIA_divisible of nat & int & 'cV[int]_dim.

Inductive QFLIA_formula :=
  | QFLIA_neg       of QFLIA_formula
  | QFLIA_and       of QFLIA_formula & QFLIA_formula
  | QFLIA_or        of QFLIA_formula & QFLIA_formula
  | QFLIA_aformula  of QFLIA_af.

Coercion QFLIA_aformula : QFLIA_af >-> QFLIA_formula.

Definition eq_QFLIA_af (f1 f2 : QFLIA_af) :=
  match f1, f2 with
    | QFLIA_leq nl tl, QFLIA_leq nr tr => (nl == nr) && (tl == tr)
    | QFLIA_divisible ml nl tl, QFLIA_divisible mr nr tr =>
      [&& (ml == mr), (nl == nr) & (tl == tr)]
    | _, _ => false
  end.

Lemma eq_QFLIA_afP : Equality.axiom eq_QFLIA_af.
Proof.
move => f1 f2; apply: (iffP idP) => [| <-].
- by case: f1 f2 => [| ml] nl tl [nr tr //= /andP | mr nr tr //= /and3P] [];
    do ! move/eqP => ->.
- by case: f1 => [| m] n t /=; rewrite !eqxx.
Qed.

Canonical QFLIA_af_eqMixin := EqMixin eq_QFLIA_afP.
Canonical QFLIA_af_eqType := Eval hnf in EqType QFLIA_af QFLIA_af_eqMixin.

Fixpoint eq_QFLIA_formula (f1 f2 : QFLIA_formula) :=
  match f1, f2 with
  | QFLIA_neg f1', QFLIA_neg f2' => eq_QFLIA_formula f1' f2'
  | QFLIA_and f1l f1r, QFLIA_and f2l f2r =>
    eq_QFLIA_formula f1l f2l && eq_QFLIA_formula f1r f2r
  | QFLIA_or f1l f1r, QFLIA_or f2l f2r =>
    eq_QFLIA_formula f1l f2l && eq_QFLIA_formula f1r f2r
  | QFLIA_aformula f1', QFLIA_aformula f2' => f1' == f2'
  | _, _ => false
  end.

Lemma eq_QFLIA_formulaP : Equality.axiom eq_QFLIA_formula.
Proof.
move => f1 f2; apply: (iffP idP) => [| <-].
- by elim: f1 f2 =>
    [f1 IHf1 | f1l IHf1l f1r IHf1r | f1l IHf1l f1r IHf1r | f1]
    [//= f2 /IHf1 -> | //= f2l f2r /andP [] /IHf1l -> /IHf1r -> |
     //= f2l f2r /andP [] /IHf1l -> /IHf1r -> | //= f2 /eqP ->].
- by elim: f1 => //= fl -> fr ->.
Qed.

Canonical QFLIA_formula_eqMixin := EqMixin eq_QFLIA_formulaP.
Canonical QFLIA_formula_eqType :=
  Eval hnf in EqType QFLIA_formula QFLIA_formula_eqMixin.

Definition QFLIA_interpret_af (I : 'cV[int]_dim) (f : QFLIA_af) : bool :=
  match f with
    | QFLIA_leq n t => (0 <= n + (t^T *m I) 0 0)%R
    | QFLIA_divisible m n t => (m.+1 %| (n + (t^T *m I) 0 0)%R)%Z
  end.

Fixpoint QFLIA_interpret_formula
         (I : 'cV[int]_dim) (f : QFLIA_formula) : bool :=
  match f with
    | QFLIA_neg f => ~~ QFLIA_interpret_formula I f
    | QFLIA_and f f' =>
      QFLIA_interpret_formula I f && QFLIA_interpret_formula I f'
    | QFLIA_or f f' =>
      QFLIA_interpret_formula I f || QFLIA_interpret_formula I f'
    | QFLIA_aformula f => QFLIA_interpret_af I f
  end.

Definition QFLIA_top : QFLIA_af := QFLIA_leq 0 0.

Lemma QFLIA_top_true (I : 'cV_dim) : QFLIA_interpret_af I QFLIA_top.
Proof. by rewrite /= trmx0 mul0mx mxE addr0. Qed.

Definition QFLIA_bot : QFLIA_af := QFLIA_leq (- 1) 0.

Lemma QFLIA_bot_false (I : 'cV_dim) : QFLIA_interpret_af I QFLIA_bot = false.
Proof. by rewrite /= trmx0 mul0mx mxE addr0. Qed.

Definition QFLIA_conj (fs : seq QFLIA_formula) := foldr QFLIA_and QFLIA_top fs.

Definition QFLIA_disj (fs : seq QFLIA_formula) := foldr QFLIA_or QFLIA_bot fs.

Lemma QFLIA_conj_all fs (I : 'cV_dim) :
  QFLIA_interpret_formula I (QFLIA_conj fs) =
  all (QFLIA_interpret_formula I) fs.
Proof. by elim: fs => [| f fs /= -> //]; apply QFLIA_top_true. Qed.

Lemma QFLIA_disj_has fs (I : 'cV_dim) :
  QFLIA_interpret_formula I (QFLIA_disj fs) =
  has (QFLIA_interpret_formula I) fs.
Proof. by elim: fs => [| f fs /= -> //]; apply QFLIA_bot_false. Qed.

Fixpoint QFLIA_NF (f : QFLIA_formula) b1 b2 : seq (seq QFLIA_af) :=
  match f with
    | QFLIA_neg f' => QFLIA_NF f' (~~ b1) (~~ b2)
    | QFLIA_and f1 f2 =>
      if b1
      then QFLIA_NF f1 b1 b2 ++ QFLIA_NF f2 b1 b2
      else [seq fs1 ++ fs2 | fs1 <- QFLIA_NF f1 b1 b2, fs2 <- QFLIA_NF f2 b1 b2]
    | QFLIA_or f1 f2 =>
      if b1
      then [seq fs1 ++ fs2 | fs1 <- QFLIA_NF f1 b1 b2, fs2 <- QFLIA_NF f2 b1 b2]
      else QFLIA_NF f1 b1 b2 ++ QFLIA_NF f2 b1 b2
    | QFLIA_aformula f' =>
      if b2
      then
        match f' with
          | QFLIA_leq n t => [:: [:: QFLIA_leq (- n - 1) (- t)]]
          | QFLIA_divisible m n t =>
            let fs := [seq QFLIA_divisible m (n + i%:R) t | i <- iota 1 m] in
            if b1 then [seq [:: f] | f <- fs] else [:: fs]
        end
      else [:: [:: f']]
  end.

Lemma QFLIA_NF_correctness' I (f : QFLIA_formula) b1 b2 :
  QFLIA_interpret_formula I f =
  \big[(if b1 then andb else orb)/b1]_(fs <- QFLIA_NF f b1 b2)
    \big[(if b1 then orb else andb)/ ~~ b1]_(af <- fs)
      (b2 (+) QFLIA_interpret_af I af).
Proof.
elim: f b1 b2 => //=.
- move => f IH b1 b2.
  by rewrite (IH (~~ b1) (~~ b2)); case: b1 => //=;
    do ! (rewrite big_has big_all -all_predC; apply eq_in_all => afs _ /=) ||
         (rewrite big_has big_all -has_predC; apply eq_in_has => af _ /=);
    rewrite addNb negbK.
- move => f1 IH1 f2 IH2 [] b2; first by rewrite big_cat /= -IH1 -IH2.
  rewrite (IH1 false b2) (IH2 false b2) big_distrlr big_allpairs /=.
  by apply eq_bigr => i _; apply eq_bigr => j _; rewrite big_cat.
- move => f1 IH1 f2 IH2 [] b2 /=; last by rewrite big_cat /= -IH1 -IH2.
  rewrite (IH1 true b2) (IH2 true b2) big_distrlr big_allpairs /=.
  by apply eq_bigr => i _; apply eq_bigr => j _; rewrite big_cat.
- move => q b1 []; last by case: b1; rewrite !big_cons !big_nil !andbT !orbF.
  case: q => [| m] n t /=;
    first by rewrite !big_cons !big_nil /= -(ltz_addr1 _ (_ - _ + _)) addrAC
                     subrK trmxN mulNmx (mxE oppmx_key) -opprD oppr_gt0 -lerNgt;
             case: b1; rewrite orbF andbT.
  suff Hdvdz x : (m.+1 %| x)%Z =
                 ~~ has (fun i => m.+1 %| (i%:Z + x)%R)%Z (iota 1 m)
    by rewrite Hdvdz -all_predC -big_all; case: b1 => /=;
       rewrite ?(big_cons, big_nil, big_map, orbF); apply eq_bigr => i _;
       rewrite ?(big_cons, big_nil, big_map, orbF) /= addrCA addrA natz.
  apply/esym/hasPn; case: ifP => [| H0] H /=; last (apply/notF; rewrite -{}H0).
  + move => i; rewrite mem_iota add1n ltnS => /andP [H0 H1].
    apply/dvdz_mod0P; rewrite -modzDmr (dvdz_mod0P H) addr0 modz_small.
    * by case: i H0 H1.
    * by rewrite lez_nat ltz_nat ltnS H1.
  + move: {H} (H `|(m.+1%:Z - (x %% m.+1)%Z)%R|).
    have H: ((x %% m.+1)%Z < m.+1)%R by rewrite ltz_pmod.
    rewrite mem_iota absz_gt0 subr_eq0 neqr_lt H orbT /= add1n ltnS.
    move: (ltrW H); rewrite -lez_nat ler_def abszE => /eqP ->.
    rewrite ler_sub_addl intS ler_add2r -intS.
    move/implyP; rewrite implybN -ltrNge -(addr0 1%R) ltz_add1r => /implyP H0.
    apply/dvdz_mod0P/eqP; rewrite eqr_le modz_ge0 // {}H0 //; apply/dvdz_mod0P.
    by rewrite -addrA modzDl addrC {1}(divz_eq x m.+1) -addrA modzMDl subrr.
Qed.

Lemma QFLIA_NF_correctness I (f : QFLIA_formula) b1 :
  QFLIA_interpret_formula I f =
  \big[(if b1 then andb else orb)/b1]_(fs <- QFLIA_NF f b1 false)
    \big[(if b1 then orb else andb)/ ~~ b1]_(af <- fs)
      (QFLIA_interpret_af I af).
Proof.
rewrite (QFLIA_NF_correctness' I f b1 false).
by apply eq_bigr => i _; apply eq_bigr => j _; rewrite addFb.
Qed.

End QFLIA.

Arguments QFLIA_top {dim}.
Arguments QFLIA_bot {dim}.

(* Quantifier elimination *)

Lemma modz_dvdm (m n d : int) : (d %| m)%Z -> ((n %% m)%Z = n %[mod d])%Z.
Proof.
by move/dvdzP => -[x ->]; rewrite {2}(divz_eq n (x * d)) mulrA modzMDl.
Qed.

Lemma ler_mod m d : (0 <= m -> 0 < d -> (m %% d)%Z <= m)%R.
Proof.
by move => H H0; rewrite {2}(divz_eq m d) ler_addr;
        apply mulr_ge0; [rewrite divz_ge0 | apply ltrW].
Qed.

Lemma dvdzE' (d m : int) : (d %| m)%Z = (m %% d == 0)%Z.
Proof. by case: dvdz_mod0P => /eqP // H; apply/eqP. Qed.

(*
Lemma elimination_principle1 (a b : int) (ds : seq (nat * int * int)) :
  reflect
    (exists x, (a <= x <= b) &&
               all (fun d => d.1.1.+1 %| d.1.2 * x + d.2)%Z ds)%R
    (@has nat
          (fun i => (a + i <= b) &&
                    all (fun d => d.1.1.+1 %| d.1.2 * (a + i) + d.2)%Z ds)
          (iota 0 (\prod_(d <- ds) d.1.1.+1)))%R.
Proof.
apply/(iffP hasP) => -[x].
- by rewrite mem_iota add0n /= => H H0; exists (a + x)%R; rewrite ler_addl.
- rewrite andbC => /and3P /= [H H0 H1].
  have H2: 0 < \prod_(d <- ds) d.1.1.+1 by apply prodn_gt0.
  exists `|(x - a) %% (\prod_(d <- ds) d.1.1.+1)%N|%Z;
    last (rewrite gez0_abs ?modz_ge0 ?lt0n_neq0 //; apply/andP; split).
  + by rewrite mem_iota add0n /=
               -ltz_nat gez0_abs ?modz_ge0 ?lt0n_neq0 // ltz_pmod.
  + apply: (ler_trans _ H1).
    by rewrite -lter_sub_addl {2}(divz_eq (x - a) (\prod_(d <- ds) d.1.1.+1)%N)
               cpr_add mulr_ge0 // divz_ge0 // subr_ge0.
  + apply/allP => -[[/= m c1] c2] Hd.
    apply/dvdz_mod0P; rewrite -modzDml -modzMmr -(modzDmr a) modz_dvdm.
    * rewrite  modzDmr modzMmr modzDml addrCA subrr addr0.
      by apply/dvdz_mod0P/(allP H _ Hd).
    * by rewrite unfold_in /= (big_rem _ Hd) /=; apply dvdn_mulr, dvdnn.
Qed.
*)

Section QE.

Variables (dim : nat)
          (fs_leq : seq (int * 'cV[int]_(1 + dim)))
          (fs_mod : seq (nat * int * 'cV[int]_(1 + dim))).

Definition prod_coef :=
  (\prod_(f <- fs_leq | f.2 0%R 0%R != 0) `|f.2 0%R 0%R|%Z *
   \prod_(f <- fs_mod | f.2 0%R 0%R != 0) `|f.2 0%R 0%R|%Z)%N.

Definition fs_leq0 :=
  pmap (fun f : int * 'cV[int]_(1 + dim) =>
          if f.2 0%R 0%R == 0 then Some (f.1, dsubmx f.2) else None)
       fs_leq.

Definition fs_leq1 (b : bool) : seq (int * 'cV[int]_dim) :=
  pmap (fun f : int * 'cV[int]_(1 + dim) =>
          if (if b then f.2 0 0 <= 0 else 0 <= f.2 0 0)%R
          then None
          else let c := (- (prod_coef %/ f.2 0 0)%Z)%R in
               Some (c * f.1, c *: dsubmx f.2)%R)
       fs_leq.

Definition fs_mod0 : seq (nat * int * 'cV[int]_dim) :=
  [seq (f.1.1, f.1.2, dsubmx f.2) |
   f : nat * int * 'cV[int]_(1 + dim) <- fs_mod & (f.2 0 0 == 0)%R].

Definition fs_mod1 : seq (nat * int * 'cV[int]_dim) :=
  (prod_coef.-1, 0, 0)%R ::
  [seq let c : int := (prod_coef%:Z %/ (f.2 0 0)%R)%Z in
       ((f.1.1.+1 * `|c|)%N.-1, f.1.2 * c, c *: dsubmx f.2)%R |
   f : nat * int * 'cV[int]_(1 + dim) <- fs_mod & (f.2 0 0 != 0)%R].

Definition prod_mod := (\prod_(f <- fs_mod1) f.1.1.+1)%N.

Definition exists_conj_elim_mod (x0 : int) (t : 'cV_dim) : QFLIA_formula dim :=
  QFLIA_conj
    [seq QFLIA_aformula
         (QFLIA_divisible fm.1.1 (fm.1.2 + x0) (fm.2 + t))
    | fm <- fs_mod1].

Definition exists_conj_elim : QFLIA_formula dim :=
  QFLIA_and
  (QFLIA_conj
     ([seq QFLIA_aformula (QFLIA_leq f.1 f.2) | f <- fs_leq0] ++
      [seq QFLIA_aformula (QFLIA_divisible f.1.1 f.1.2 f.2)  | f <- fs_mod0]))
  (if nilp (fs_leq1 false) || nilp (fs_leq1 true)
   then QFLIA_disj
          [seq exists_conj_elim_mod i 0 | i : nat <- iota 0 prod_mod]
   else QFLIA_conj
          [seq QFLIA_disj
               [seq QFLIA_and
                    (QFLIA_leq (fl.1 - fr.1 - i%:Z) (fl.2 - fr.2))
                    (exists_conj_elim_mod (fr.1 + i) fr.2)
               | i : nat <- iota 0 prod_mod]
          | fl <- fs_leq1 false, fr <- fs_leq1 true]).

Lemma prod_coef_gt0 : 0 < prod_coef.
Proof.
by rewrite muln_gt0; apply/andP; split;
  apply/prodn_cond_gt0 => i H; rewrite absz_gt0.
Qed.

Lemma prod_coef_cml :
  all (fun f : int * 'cV[int]_(1 + dim) =>
         (f.2 0 0 == 0)%R || (f.2 0%R 0%R %| prod_coef%:Z))%Z fs_leq.
Proof.
apply/allP => -[/= n t] H.
rewrite -(negbK (_ == _)) -implybE /prod_coef.
apply/implyP => H0.
rewrite (big_rem _ H) /= H0 !PoszM -mulrA; apply dvdz_mulr.
by rewrite dvdzE absz_id dvdnn.
Qed.

Lemma prod_coef_cmm :
  all (fun f : nat * int * 'cV[int]_(1 + dim) =>
         (f.2 0 0 == 0)%R || (f.2 0%R 0%R %| prod_coef%:Z))%Z fs_mod.
Proof.
apply/allP => -[/= n t] H.
rewrite -(negbK (_ == _)) -implybE /prod_coef.
apply/implyP => H0.
rewrite (big_rem _ H) /= H0 !PoszM mulrCA; apply dvdz_mulr.
by rewrite dvdzE absz_id dvdnn.
Qed.

Lemma prod_mod_divisor f : f \in fs_mod1 -> (f.1.1.+1 %| prod_mod%:Z)%Z.
Proof.
move => Hf.
rewrite /prod_mod (eq_big_perm _ (perm_to_rem Hf)) /= big_cons PoszM mulrC.
by apply dvdz_mull.
Qed.

Lemma fs_leq_correct x I :
  all (QFLIA_interpret_af (col_mx (const_mx x) I))
      [seq QFLIA_leq f.1 f.2 | f <- fs_leq] =
  [&& all (QFLIA_interpret_af I) [seq QFLIA_leq f.1 f.2 | f <- fs_leq0],
   all (fun f => prod_coef%:Z * x <= f.1 + (f.2^T *m I) 0 0)%R
       (fs_leq1 false) &
   all (fun f => f.1 + (f.2^T *m I) 0 0 <= prod_coef%:Z * x)%R
       (fs_leq1 true)].
Proof.
rewrite /fs_leq0 /fs_leq1 !(all_pmap, all_map) -!all_predI.
apply eq_in_all => -[/= n t] Hf.
rewrite -(vsubmxK t) tr_col_mx (mxE col_mx_key);
  case: splitP => // j _;
  rewrite ord1 {j} vsubmxK mul_row_col 2!mxE big_ord1 3!mxE lshift0.
by (case: (ltrgtP (t 0 0) 0)%R (allP prod_coef_cml _ Hf);
      last by move => -> _ /=; rewrite mul0r add0r andbT);
  rewrite dvdz_eq => /= H /eqP H0;
  rewrite ?andbT trmx_scale -scalemxAl (mxE scalemx_key) -mulrDr
          -1?[RHS](ler_nmul2l H) -1?[RHS](ler_pmul2l H) mulrA mulrN
          [X in (- X)%R](mulrC (t _ _)) H0 mulNr -mulrN mulrCA ler_pmul2l
          ?ltz_nat ?prod_coef_gt0 // -(subr_ge0 (- _)%R) opprK (addrCA n).
Qed.

Lemma fs_mod_correct x I :
  all (QFLIA_interpret_af (col_mx (const_mx x) I))
      [seq QFLIA_divisible f.1.1 f.1.2 f.2 | f <- fs_mod] =
  all (QFLIA_interpret_af I)
      [seq QFLIA_divisible f.1.1 f.1.2 f.2 | f <- fs_mod0] &&
  all (fun f : nat * int * 'cV[int]_dim =>
       f.1.1.+1 %|
                (f.1.2 + prod_coef%:Z * x + (f.2^T *m I) 0 0)%R)%Z
      fs_mod1.
Proof.
rewrite /fs_mod0 /fs_mod1 /= !(all_pmap, all_filter, all_map)
        prednK ?prod_coef_gt0 //
        add0r trmx0 mul0mx mxE addr0 dvdz_mulr ?dvdzz //= -all_predI.
apply eq_in_all => /= -[[d n] t] Hf /=.
rewrite -{1}(vsubmxK t) tr_col_mx mul_row_col 2!mxE big_ord1 3!mxE lshift0.
case_eq (t 0%R 0%R == 0%R) => H; rewrite H /=;
  first by rewrite andbT (eqP H) mul0r add0r.
move: (allP prod_coef_cmm _ Hf) prod_coef_gt0.
rewrite H /= => /dvdzP [prod_coef' H0] /lt0n_neq0.
rewrite -eqz_nat H0 mulzK ?H // mulf_eq0 H /= orbF => H1.
by rewrite prednK ?ltz_nat ?muln_gt0 /= ?absz_gt0 //
           trmx_scale -scalemxAl (mxE scalemx_key) -mulrA (mulrC n) -!mulrDr
           [RHS]dvdzE PoszM abszM /(`|Posz `|_| |) -abszM -dvdzE
           (mulrC _%:Z%Z) dvdz_mul2l // addrA.
Qed.

Lemma exists_conj_elim_mod_correct (x : int) t (I : 'cV_dim) :
  QFLIA_interpret_formula I (exists_conj_elim_mod x t) =
  all (fun f : nat * int_Ring * 'cV_dim =>
         (f.1.1.+1 %| (f.1.2 + x + ((f.2 + t)^T *m I) 0 0)%R)%Z)
      fs_mod1.
Proof. by rewrite QFLIA_conj_all all_map; apply (eq_in_all (s := fs_mod1)). Qed.

Lemma exists_conj_elimP I :
  reflect
    (exists x,
        all (QFLIA_interpret_af (col_mx (const_mx x) I))
            ([seq QFLIA_leq f.1 f.2 | f <- fs_leq] ++
             [seq QFLIA_divisible f.1.1 f.1.2 f.2 | f <- fs_mod]))
    (QFLIA_interpret_formula I exists_conj_elim).
Proof.
set bs := fun fl => [seq (true, f.1 + (f.2^T *m I) 0 0)%R | f <- fs_leq1 fl].
set P := fun x => all
  (fun f => f.1.1.+1 %| (f.1.2 + x + (f.2^T *m I) 0 0)%R)%Z fs_mod1.
have H_prodm : (0 < prod_mod%:Z)%R by rewrite ltz_nat prodn_gt0.
have H_periodm x : P x = P (prod_mod%:Z + x)%R
  by apply eq_in_all => /= f Hf; rewrite !dvdzE'; congr eq_op; apply/esym/eqP;
     rewrite eqz_mod_dvd addrCA -2!(addrA prod_mod%:Z%Z) subrr addr0;
     apply prod_mod_divisor.
move: (periodic_qe_principle int_archi (bs true) (bs false) H_prodm H_periodm).
set F1 := exists x : int, _.
set F2 := exists x : int, _.
have: F1 <->
      all (QFLIA_interpret_af I)
        ([seq (QFLIA_leq f.1 f.2) | f <- fs_leq0] ++
         [seq (QFLIA_divisible f.1.1 f.1.2 f.2)  | f <- fs_mod0])
      /\ F2
  by subst F1 F2 bs P; split;
    [case => x H; split; last exists (prod_coef%:Z * x)%R; move: H |
     case => H0 [x' H];
     (have/dvdzP [x]: (prod_coef %| x')%Z
        by move/and3P: H => [_ _] /= /andP [H _]; move: H;
           rewrite add0r trmx0 mul0mx mxE addr0; congr dvdz;
           move: prod_coef_gt0; case: prod_coef);
     rewrite mulrC => Hx'; subst x'; exists x; move: H0 H];
  rewrite !all_cat fs_leq_correct fs_mod_correct;
  [by move => /andP [] /and3P [] -> _ _ /andP [] |
   move => /andP [] /and3P [_ H H0] /andP [_ H1] |
   move => /andP [-> ->] /and3P [H H0 H1]; rewrite !andTb -andbA];
  move/and3P: (And3 H0 H H1); congr [&& _, _ & _];
  rewrite ?all_map; apply eq_in_all => f Hf //=; rewrite mulrCA mulrA.
move => H H0.
move: {H H0} (iff_trans H (and_iff_compat_l _ H0)) => H1.
apply: (equivP _ (iff_sym H1)) => {H1}; subst F1 F2.
rewrite /exists_conj_elim /= QFLIA_conj_all !all_cat !all_map.
Opaque fs_leq0 fs_leq1 fs_mod0 fs_mod1.
apply (iffP andP) => -[H0 H]; (split; first apply H0);
  move: {H0} H; rewrite /bs /nilp !size_map -!/(nilp _) orbC;
  case: ifP => _.
- rewrite QFLIA_disj_has has_map => /hasP [i].
  rewrite mem_iota /= add0n exists_conj_elim_mod_correct /= => H H0.
  by exists i; apply/allP => /= f /(allP H0) /=; rewrite addr0.
- rewrite QFLIA_conj_all => /all_allpairsP /= H lb ub.
  move => /mapP [/= j Hj -> {lb}] /mapP [/= i Hi -> {ub}].
  move: (H i j Hi Hj); rewrite QFLIA_disj_has has_map => /hasP [/= k].
  rewrite mem_iota /= add0n exists_conj_elim_mod_correct => H0 /andP [H1 H2].
  exists (j.1 + (j.2^T *m I) 0 0 + k)%R; move: H1.
  rewrite -{1}(addr0 (j.1 + _)%R) ler_add2l /=
          trmxD trmxN mulmxDl mulNmx mxE (mxE oppmx_key) addrA
          2!(addrAC _ (- k%:Z)%R) (addrAC _ (- j.1)%R) -2!addrA -2!opprD addrA
          subr_ge0 => -> /=.
  apply/allP => /= f; move/(allP H2); congr dvdz.
  by rewrite trmxD mulmxDl mxE (addrAC j.1) !addrA addrAC.
- case => x Hx; rewrite QFLIA_disj_has has_map; apply/hasP.
  exists `|x %% prod_mod|%Z => /=.
  + rewrite mem_iota /= add0n -ltz_nat gez0_abs; first by apply ltz_pmod.
    by apply modz_ge0; rewrite eqz_nat; apply lt0n_neq0.
  + rewrite exists_conj_elim_mod_correct gez0_abs;
      last by apply modz_ge0; rewrite eqz_nat; apply lt0n_neq0.
    apply/allP => /= f Hf; move: (allP Hx _ Hf).
    rewrite addr0 !dvdzE'; congr eq_op; apply/eqP.
    rewrite eqz_mod_dvd !(addrC f.1.2) -!(addrA _ f.1.2)
            opprD addrA (addrAC x) -addrA subrr addr0 -eqz_mod_dvd modz_dvdm //.
    by apply prod_mod_divisor.
- move => H; rewrite QFLIA_conj_all; apply/all_allpairsP => /= i j Hi Hj.
  case: {H} (H _ _ (map_f _ Hj) (map_f _ Hi)) => x /and3P [/= H H0 H1].
  rewrite QFLIA_disj_has has_map; apply/hasP.
  exists `|(x - (j.1 + (j.2^T *m I) 0%R 0%R))%R %% prod_mod|%Z;
    last (rewrite /= gez0_abs ?modz_ge0 // ?eqz_nat ?lt0n_neq0 //;
          apply/andP; split => /=).
  + by rewrite mem_iota /= add0n -ltz_nat gez0_abs ?ltz_pmod //;
       apply modz_ge0; rewrite eqz_nat; apply lt0n_neq0.
  + rewrite trmxD trmxN mulmxDl mulNmx (mxE addmx_key) (mxE oppmx_key).
    rewrite addrA 3!(addrAC _ (- _)%R) -2!addrA -!opprD subr_ge0.
    apply: (ler_trans _ H0).
    rewrite -subr_ge0 addrA (opprD (_ + _)%R) addrA subr_ge0.
    by apply ler_mod => //; rewrite subr_ge0.
  + rewrite exists_conj_elim_mod_correct;
      apply/allP => /= f Hf; move: (allP H1 _ Hf);
      rewrite !dvdzE'; congr eq_op; apply/eqP.
    rewrite addrAC trmxD mulmxDl (mxE addmx_key) addrA (addrAC f.1.2 (_ + _)%R)
            -(addrA (f.1.2 + _)%R) eqz_modDl eqz_mod_dvd
            (addrAC j.1) opprD addrA -eqz_mod_dvd modz_dvdm //.
    by apply prod_mod_divisor.
Qed.

End QE.
