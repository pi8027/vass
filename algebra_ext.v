From mathcomp Require Import all_ssreflect all_algebra.
Require Import utils.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma addr_lteif0r b (R : numDomainType) (x y : R) :
  (0 < x + y ?<= if b)%R = (- x < y ?<= if b)%R.
Proof. by rewrite addrC -{1}(opprK x) subr_lteif0r. Qed.

(******************************************************************************)
(*  extensions for interval                                                   *)
(******************************************************************************)

Section IntervalPo.

Local Open Scope order_scope.

Variable (disp : unit) (T : porderType disp).
Notation itv_bound := (itv_bound T).
Notation interval := (interval T).

Definition itv_isinf (i : interval) :=
  match i with
    | Interval (BInfty false) _ | Interval _ (BInfty true) => false
    | Interval (BInfty true) _ | Interval _ (BInfty false) => true
    | _ => false
  end.

Definition itv_nonempty (i : interval) :=
  match i with
    | Interval (BSide lb lr) (BSide ub ur) => lr < ur ?<= if lb && ~~ ub
    | Interval (BInfty false) _ | Interval _ (BInfty true) => false
    | Interval (BInfty true) _ | Interval _ (BInfty false) => true
  end.

End IntervalPo.

Section IntervalLattice.

Local Open Scope order_scope.

Variable (disp : unit) (T : latticeType disp).

Lemma in_itv_bigI S x (s : seq S) (f : S -> interval T) :
  (x \in \big[Order.meet/`]-oo, +oo[%O]_(ix <- s) f ix) =
  all (fun ix => x \in f ix) s.
Proof.
by rewrite -big_all; apply/(big_morph (fun i => x \in i)); first exact: in_itvI.
Qed.

End IntervalLattice.

Section IntervalTotal.

Local Open Scope order_scope.

Variable (disp : unit) (T : orderType disp).

Lemma itv_total_meetsE (S : Type) (s : seq S) (f : S -> interval T) :
  \meet_(ix <- s) f ix \in
  `]-oo, +oo[ :: [seq f ix `&` f ix' | ix <- s, ix' <- s].
Proof.
case: s => [|x s]; rewrite ?big_nil // inE; apply/orP; right.
elim: s x => [|y s ih] x; rewrite !big_cons;
  first by rewrite big_nil meetx1 inE meetxx.
move: (itv_total_meet3E (f x) (f y) (\meet_(ix <- s) f ix)).
rewrite meetA 3!inE => /or3P [] /eqP ->.
- by rewrite /= !inE eqxx orbT.
- move: (ih x); rewrite big_cons 2!allpairs_consr 2!mem_cat allpairs_consr /=.
  by rewrite !(mem_cat, inE) -!orbA => /or4P [] ->; rewrite ?orbT.
- move: (ih y); rewrite big_cons 2!allpairs_consr 2!mem_cat allpairs_consr /=.
  by rewrite !(mem_cat, inE) -!orbA => /or4P [] ->; rewrite ?orbT.
Qed.

Lemma itv_total_joinsE (S : Type) (s : seq S) (f : S -> interval T) :
  \join_(ix <- s) f ix \in
  Interval +oo -oo :: [seq f ix `|` f ix' | ix <- s, ix' <- s].
Proof.
case: s => [|x s]; rewrite ?big_nil // inE; apply/orP; right.
elim: s x => [|y s ih] x; rewrite !big_cons;
  first by rewrite big_nil joinx0 inE joinxx.
move: (itv_total_join3E (f x) (f y) (\join_(ix <- s) f ix)).
rewrite joinA 3!inE => /or3P [] /eqP ->.
- by rewrite /= !inE eqxx orbT.
- move: (ih x); rewrite big_cons 2!allpairs_consr 2!mem_cat allpairs_consr /=.
  by rewrite !(mem_cat, inE) -!orbA => /or4P [] ->; rewrite ?orbT.
- move: (ih y); rewrite big_cons 2!allpairs_consr 2!mem_cat allpairs_consr /=.
  by rewrite !(mem_cat, inE) -!orbA => /or4P [] ->; rewrite ?orbT.
Qed.

End IntervalTotal.

Local Open Scope ring_scope.

Arguments itv_nonempty {disp T} i.

Lemma itv_nonemptyP (R : numFieldType) (i : interval R) :
  reflect (exists x, x \in i) (itv_nonempty i).
Proof.
case: i => [] [c1 x|[]] [c2 z|[]]; apply/(iffP idP) => [|[y /andP[]]] //=.
- by move=> hxz; exists ((x + z) / 2%:R); apply: mid_in_itv.
- exact: lteif_trans.
- by exists (x + 1); rewrite in_itv lteifS // ltr_addl ltr01.
- by exists (z - 1); rewrite in_itv lteifS // gtr_addl ltrN10.
- by exists 0.
Qed.

Lemma itv_bigI_pairwiseP
    disp (I : eqType) (T : orderType disp) (s : seq I) (f : I -> interval T) P :
  (exists x, all (fun i => x \in f i) s && P x) <->
  ((exists x, P x) /\
   (forall i j, i \in s -> j \in s ->
      exists x, [&& x \in f i, x \in f j & P x])).
Proof.
split=> [[x] /andP [Hx HPx]|[[x' Px'] H]].
- by split=> [|i j Hi Hj]; exists x; rewrite // (allP Hx _ Hi) (allP Hx _ Hj).
- case/predU1P: (itv_total_meetsE s f) => [|/allpairsP [[i j]/=[hi hj]]] hbigI;
    first by exists x'; rewrite -in_itv_bigI hbigI.
  case: (H _ _ hi hj) => x /and3P [hi' hj' Px]; exists x.
  by rewrite -in_itv_bigI hbigI in_itvI hi' hj'.
Qed.

Lemma itv_bigI_pairwise0
      (I : eqType) (R : realFieldType) (s : seq I) (f : I -> interval R) :
  itv_nonempty (\big[Order.meet/`]-oo, +oo[]_(i <- s) f i) =
  all itv_nonempty [seq f i1 `&` f i2 | i1 <- s, i2 <- s]%O.
Proof.
apply/itv_nonemptyP/all_allpairsP => [|H].
- case=> x; rewrite in_itv_bigI => /allP Hs i j Hi Hj.
  by apply/itv_nonemptyP; exists x; rewrite in_itvI !Hs.
- case/predU1P: (itv_total_meetsE s f) => [|/allpairsP [[i j] /= [hi hj]]] ->;
    first by exists 0.
  by case/itv_nonemptyP: (H _ _ hi hj) => x; exists x.
Qed.

(******************************************************************************)
(*  Archimedean axiom for numDomainType                                       *)
(******************************************************************************)

Lemma int_archi :
  forall x : int, (0 < x) -> forall y : int, exists c, (y < x *+ c).
Proof.
move=> x Hx y; exists (absz (1 + (y %/ x)%Z)).
rewrite -mulr_natr mulrC -ltz_divLR // natz.
by case: (y %/ x)%Z => //= x'; rewrite ltz_nat.
Qed.

Section periodic_itv_inf.
Variable (R : numDomainType) (period : R) (P : pred R).
Variable (period_noninfinitesimal : forall y : R, exists c, y < period *+ c).
Variable (P_periodic : forall x : R, P (period + x) = P x).

Lemma periodic_itv_inf i :
  itv_isinf i -> (exists x, P x) -> exists x, (x \in i) && P x.
Proof.
case: i => -[bl lb|[]] [bu ub|[]] //= _ [x Hx].
- case: (period_noninfinitesimal (lb - x)) => c Hc.
  exists (x + period *+ c); rewrite in_itv andbT; apply/andP; split.
  + by apply: lteifS; rewrite addrC -ltr_sub_addr.
  + by elim: c {Hc} => [|c ?];
      rewrite ?mulr0n ?addr0 // mulrS addrCA P_periodic.
- case: (period_noninfinitesimal (x - ub)) => c Hc.
  exists (x - period *+ c); rewrite in_itv; apply/andP; split.
  + by apply: lteifS; rewrite ltr_sub_addr addrC -ltr_sub_addr.
  + elim: c {Hc} => [|c IH]; first by rewrite mulr0n subr0.
    by rewrite -P_periodic addrCA mulrS opprD (addrA period) subrr sub0r.
Qed.

End periodic_itv_inf.

Section periodic_qe_principle.

Variable (R : realDomainType) (period : R) (P : pred R).
Variable (period_noninfinitesimal : forall y : R, exists c, y < period *+ c).
Variable (P_periodic : forall x : R, P (period + x) = P x).

Lemma periodic_qe_principle (lbs ubs : seq (bool * R)) :
  (exists x : R, [&& all (fun lb => lb.2 < x ?<= if lb.1) lbs,
                     all (fun ub => x < ub.2 ?<= if ub.1) ubs & P x]) <->
  if nilp lbs || nilp ubs
  then exists x : R, P x
  else (forall (lb ub : bool * R), lb \in lbs -> ub \in ubs ->
        exists x : R, [&& lb.2 < x ?<= if lb.1, x < ub.2 ?<= if ub.1 & P x]).
Proof.
split=> [|H]; first by
  case=> x /and3P [Hlb Hub HP]; case: ifP => [Hnil|Hnil lb ub Hlb' Hub'];
  exists x; rewrite // (allP Hlb _ Hlb') (allP Hub _ Hub').
have Hperiod: exists x, P x.
  case: lbs ubs H => [|lb ?] [|ub ?] //= /(_ lb ub); rewrite !inE !eqxx.
  by case=> // x /and3P [_ _ ?]; exists x.
set lbs' := [seq Interval (BSide lb.1 lb.2) (BInfty _ false) | lb <- lbs].
set ubs' := [seq Interval (BInfty _ true) (BSide (~~ ub.1) ub.2) | ub <- ubs].
suff [x /andP [H0 H1]]: exists x, all (fun i => x \in i) (lbs' ++ ubs') && P x.
  exists x; move: H0; rewrite H1 andbT {}/lbs' {}/ubs' all_cat !all_map.
  by congr andb; apply: eq_in_all => b _ /=; rewrite in_itv (negbK, andbT).
apply/itv_bigI_pairwiseP; split=> //= i' j'; rewrite !mem_cat.
by move=> /orP [] /mapP [i Hi Hi'] /orP [] /mapP [j Hj Hj'];
  (try by case: (periodic_itv_inf _ P_periodic (i := i' `&` j')%O _ Hperiod);
     rewrite ?(Hi', Hj') => // x Hx; exists x; rewrite andbA -in_itvI);
  move: H Hi Hj; do 2 case: nilP=> [-> //| _]; move => /= H Hi Hj;
  [move: (H i j Hi Hj) | move: (H j i Hj Hi)];
  case=> x H0; exists x; rewrite Hi' Hj' !in_itv andbT negbK //= andbCA.
Qed.

End periodic_qe_principle.
