Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp.
Require Import utils bigop_ext matrix_ext.
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

Definition eq_QFLIA_af (f1 f2 : QFLIA_af) :=
  match f1, f2 with
    | QFLIA_leq nl tl, QFLIA_leq nr tr => (nl == nr) && (tl == tr)
    | QFLIA_divisible ml nl tl, QFLIA_divisible mr nr tr =>
      [&& (ml == mr), (nl == nr) & (tl == tr)]
    | _, _ => false
  end.

Lemma eq_QFLIA_afP : Equality.axiom eq_QFLIA_af.
Proof.
move => t1 t2; apply: (iffP idP) => [| <-].
- by case: t1 t2 => [| ml] nl tl [nr tr //= /andP | mr nr tr //= /and3P] [];
    do ! move/eqP => ->.
- by case: t1 => [| m] n t /=; rewrite !eqxx.
Qed.

Canonical QFLIA_af_eqMixin := EqMixin eq_QFLIA_afP.
Canonical QFLIA_af_eqType := Eval hnf in EqType QFLIA_af QFLIA_af_eqMixin.

Inductive QFLIA_formula :=
  | QFLIA_neg       of QFLIA_formula
  | QFLIA_and       of QFLIA_formula & QFLIA_formula
  | QFLIA_or        of QFLIA_formula & QFLIA_formula
  | QFLIA_aformula  of QFLIA_af.

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

Definition QFLIA_top : QFLIA_formula := QFLIA_aformula (QFLIA_leq 0 0).

Lemma QFLIA_top_true (I : 'cV_dim) : QFLIA_interpret_formula I QFLIA_top.
Proof. by rewrite /= mxE add0r; apply sumr_ge0 => i _; rewrite !mxE mul0r. Qed.

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
  have Hdvdz x : (m.+1 %| x)%Z =
                 ~~ has (fun i => m.+1 %| (Posz i + x)%R)%Z (iota 1 m).
    apply/esym/hasPn; case: ifP => [| H0] H /=;
      last (apply/notF; rewrite -{}H0).
    + move => i; rewrite mem_iota add1n ltnS => /andP [H0 H1].
      apply/dvdz_mod0P; rewrite -modzDmr (dvdz_mod0P H) addr0 modz_small.
      * by case: i H0 H1.
      * by rewrite lez_nat ltz_nat ltnS H1.
    + move: {H} (H `|(Posz m.+1 - (x %% m.+1)%Z)%R|).
      have H: ((x %% m.+1)%Z < m.+1)%R by rewrite ltz_pmod.
      rewrite mem_iota absz_gt0 subr_eq0 neqr_lt H orbT /= add1n ltnS.
      move: (ltrW H); rewrite -lez_nat ler_def abszE => /eqP ->.
      rewrite ler_sub_addl intS ler_add2r -intS.
      move/implyP; rewrite implybN -ltrNge -(addr0 1%R) ltz_add1r => /implyP H0.
      apply/dvdz_mod0P/eqP; rewrite eqr_le modz_ge0 // {}H0 //.
      by apply/dvdz_mod0P;
        rewrite -addrA modzDl addrC {1}(divz_eq x m.+1) -addrA modzMDl subrr.
  rewrite Hdvdz -all_predC -big_all.
  by case: b1 => /=;
     rewrite ?(big_cons, big_nil, big_map, orbF); apply eq_bigr => i _;
     rewrite ?(big_cons, big_nil, big_map, orbF) /= addrCA addrA natz.
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

(* Quantifier elimination *)

Lemma modz_dvdm (m n d : int) : (d %| m)%Z -> ((n %% m)%Z = n %[mod d])%Z.
Proof.
by move/dvdzP => -[x ->]; rewrite {2}(divz_eq n (x * d)) mulrA modzMDl.
Qed.

Lemma elimination_principle (a b c : int) (d : nat) :
  reflect
    (exists x, (a <= x <= b) && (d.+1 %| x + c)%Z)%R
    (has (fun i : nat => (a + i <= b) && (d.+1 %| a + i + c)%Z)%R
         (iota 0 d.+1)).
Proof.
apply/(iffP hasP) => -[x].
- by rewrite mem_iota add0n /= => H H0; exists (a + x)%R; rewrite ler_addl.
- rewrite andbC => /and3P [H H0 H1].
  exists `|(x - a) %% d.+1|%Z;
    last (rewrite gez0_abs ?modz_ge0 //; apply/andP; split).
  + by rewrite mem_iota add0n /= -ltz_nat gez0_abs ?modz_ge0 // ltz_pmod.
  + apply: (ler_trans _ H1).
    by rewrite -lter_sub_addl {2}(divz_eq (x - a) d.+1)
               cpr_add mulr_ge0 // divz_ge0 // subr_ge0.
  + by apply/dvdz_mod0P;
       rewrite addrAC modzDmr addrAC (addrC a) addrNK; apply/dvdz_mod0P.
Qed.

Lemma elimination_principle' (a b : int) (ds : seq (nat * int)) :
  reflect
    (exists x, (a <= x <= b) && all (fun d => d.1.+1 %| x + d.2)%Z ds)%R
    (has (fun i : nat => (a + i <= b) &&
                         all (fun d => d.1.+1 %| a + i + d.2)%Z ds)
         (iota 0 (\prod_(d <- ds) d.1.+1)))%R.
Proof.
apply/(iffP hasP) => -[x].
- by rewrite mem_iota add0n /= => H H0; exists (a + x)%R; rewrite ler_addl.
- rewrite andbC => /and3P /= [H H0 H1].
  have H2: 0 < \prod_(d <- ds) d.1.+1 by apply prodn_cond_gt0.
  exists `|(x - a) %% (\prod_(d <- ds) d.1.+1)%N|%Z;
    last (rewrite gez0_abs ?modz_ge0 ?lt0n_neq0 //; apply/andP; split).
  + by rewrite mem_iota add0n /=
               -ltz_nat gez0_abs ?modz_ge0 ?lt0n_neq0 // ltz_pmod.
  + apply: (ler_trans _ H1).
    by rewrite -lter_sub_addl {2}(divz_eq (x - a) (\prod_(d <- ds) d.1.+1)%N)
               cpr_add mulr_ge0 // divz_ge0 // subr_ge0.
  + apply/allP => -[/= d c] Hd.
    apply/dvdz_mod0P; rewrite addrAC -modzDmr modz_dvdm.
    * rewrite modzDmr addrAC (addrC a) addrNK.
      by apply/dvdz_mod0P/(allP H (d, c) Hd).
    * by rewrite unfold_in /= (big_rem _ Hd) /=; apply dvdn_mulr, dvdnn.
Qed.
