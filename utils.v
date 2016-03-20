Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma split_lshift (m n : nat) (i : 'I_m) : split (lshift n i) = inl i.
Proof. by apply: unsplitK (inl i). Qed.

Lemma split_rshift (m n : nat) (i : 'I_n) : split (rshift m i) = inr i.
Proof. by apply: unsplitK (inr i). Qed.

Section cat_tuple.

Variable (A : Type) (n m : nat).

Definition cat_tuple (t1 : A ^ n) (t2 : A ^ m) : A ^ (n + m) :=
  [ffun i => match split i with
             | inl i' => t1 i'
             | inr i' => t2 i'
             end].

Definition split_tuple (t : A ^ (n + m)) : A ^ n * A ^ m :=
  ([ffun i => t (lshift m i)], [ffun i => t (rshift n i)]).

Lemma cat_tuple_lshift (t1 : A ^ n) (t2 : A ^ m) i :
  cat_tuple t1 t2 (lshift m i) = t1 i.
Proof. by rewrite ffunE split_lshift. Qed.

Lemma cat_tuple_rshift (t1 : A ^ n) (t2 : A ^ m) i :
  cat_tuple t1 t2 (rshift n i) = t2 i.
Proof. by rewrite ffunE split_rshift. Qed.

End cat_tuple.

Section cons_tuple.

Variable (A : Type) (n : nat).

Definition cons_tuple (h : A) (t : A ^ n) : A ^ n.+1 :=
  [ffun m => match @split 1 n m with
               | inl _ => h
               | inr i => t i
             end].

Definition tail_tuple (t : A ^ n.+1) : A ^ n := [ffun m => t (rshift 1 m)].

Lemma cons_tuple_eq1 (h : A) (t : A ^ n) : cons_tuple h t ord0 = h.
Proof. by rewrite /cons_tuple ffunE; case: splitP. Qed.

Lemma cons_tuple_eq2 (h : A) (t : A ^ n) (i : 'I_n) :
  cons_tuple h t (rshift 1 i) = t i.
Proof. by rewrite /cons_tuple ffunE split_rshift. Qed.

Lemma tail_tuple_eq (t : A ^ n.+1) (i : 'I_n) : tail_tuple t i = t (rshift 1 i).
Proof. by rewrite /tail_tuple ffunE. Qed.

Lemma tail_cons_tuple (h : A) (t : A ^ n) : tail_tuple (cons_tuple h t) = t.
Proof. by apply/ffunP => /= i; rewrite !ffunE split_rshift. Qed.

Lemma cons_tail_tuple (t : A ^ n.+1) : cons_tuple (t ord0) (tail_tuple t) = t.
Proof.
  apply/ffunP => /= i; rewrite !ffunE; case: splitP => j Hj.
  - by congr fun_of_fin; apply/val_inj; rewrite /= {}Hj; case: j => -[].
  - by rewrite ffunE; congr fun_of_fin; apply/val_inj.
Qed.

Lemma cons_tuple_const (x : A) : cons_tuple x [ffun => x] = [ffun => x].
Proof.
  apply/ffunP => /= i; rewrite /cons_tuple !ffunE.
  by case: splitP => //= i' _; rewrite ffunE.
Qed.

End cons_tuple.

Lemma cat_cons_tuple (A : Type) n m (h : A) (t1 : A ^ n) (t2 : A ^ m) :
  cat_tuple (cons_tuple h t1) t2 = cons_tuple h (cat_tuple t1 t2).
Proof.
apply/esym/ffunP => /= i; rewrite !ffunE.
case: splitP => j Hj; last case: splitP => k Hk.
- suff ->: i = (lshift m ord0) by rewrite split_lshift cons_tuple_eq1.
  by apply/val_inj => /=; rewrite {}Hj; case: j => -[].
- rewrite !ffunE.
  have: j < n by rewrite -add1n -Hj {}Hk; case: k.
  case: splitP => // l Hl _.
  have: ~~ (k < 1) by rewrite -Hk Hj.
  case: (@splitP 1 n) => // l' Hl' _; congr fun_of_fin.
  by apply/val_inj/succn_inj; rewrite /= -Hl -add1n -Hj -(add1n l') -Hl'.
- rewrite !ffunE.
  have: ~~ (j < n) by rewrite -add1n -Hj Hk -ltnNge leq_addr.
  case: splitP => // l Hl _; congr fun_of_fin.
  by apply/val_inj/(@addnI n.+1); rewrite /= -Hk Hj Hl add1n addSn.
Qed.

Lemma cons_tuple_map (A B : Type) (f : A -> B) n (h : A) (t : 'I_n -> A) :
  [ffun i => f ((cons_tuple h [ffun i => t i]) i)] =
  cons_tuple (f h) [ffun i => f (t i)].
Proof.
  apply/ffunP => /= i; rewrite !ffunE.
  by case: splitP => //= i' _; rewrite !ffunE.
Qed.

Lemma all_allpairsP
      (S T R : eqType) (g : pred R) (f : S -> T -> R) (s : seq S) (t : seq T) :
  reflect (forall (i : S) (j : T), i \in s -> j \in t -> g (f i j))
          (all g [seq f i j | i <- s, j <- t]).
Proof.
  apply (iffP allP).
  - by move => H i j H0 H1; apply/H/allpairsP; exists (i, j).
  - by move => H x /allpairsP [] [i j] [] /= H0 H1 ->; apply H.
Qed.

Lemma all_enum (T : finType) (P : pred T) : all P (enum T) = [forall i, P i].
Proof.
  apply/idP; case: ifP; first by move/forallP => H; apply/allP.
  by move/negP => H /allP H0; apply: H;
    apply/forallP => x; apply: H0; rewrite mem_enum.
Qed.

(******************************************************************************)
(*  extensions for fintype                                                    *)
(******************************************************************************)

Import GRing.Theory Num.Theory.

Section Range.
Variable (i k : int).

Inductive range : predArgType := Range j of (i <= j <= k)%R.

Coercion int_of_range r := let: (Range j _) := r in j.

Lemma lb_range (r : range) : (i <= r)%R. Proof. by case r => /= j /andP []. Qed.
Lemma ub_range (r : range) : (r <= k)%R. Proof. by case r => /= j /andP []. Qed.

Canonical range_subType := [subType for int_of_range].
Definition range_eqMixin := Eval hnf in [eqMixin of range by <:].
Canonical range_eqType := Eval hnf in EqType range range_eqMixin.
Definition range_choiceMixin := [choiceMixin of range by <:].
Canonical range_choiceType := Eval hnf in ChoiceType range range_choiceMixin.
Definition range_countMixin := [countMixin of range by <:].
Canonical range_countType := Eval hnf in CountType range range_countMixin.
Canonical range_subCountType := [subCountType of range].

Definition range_enum : seq range :=
  pmap insub
    (map Negz (match i with Negz i' => iota 0 i'.+1 | _ => [::] end) ++
     map Posz (match k with Posz k' => iota 0 k'.+1 | _ => [::] end)).

Lemma range_enum_uniq : uniq range_enum.
Proof.
  rewrite pmap_sub_uniq // cat_uniq !map_inj_in_uniq;
    first (case: i => i'; case: k => k'; rewrite ?iota_uniq // andTb andbT).
  - by rewrite -all_predC /=; elim: map.
  - rewrite -all_predC all_map.
    by elim: (iota 0 k'.+1) => //= n ns ->; rewrite andbT !inE /=; elim: iota.
  - by move => /= x y _ _ [].
  - by move => /= x y _ _ [].
Qed.

Lemma mem_range_enum r : r \in range_enum.
Proof.
  rewrite -(mem_map val_inj) /= /range_enum.
  case: r => /= j /andP [H H0]; rewrite pmap_filter;
    last by move => j'; case: insubP.
  rewrite mem_filter mem_cat; apply/andP; split;
    first by case: insubP => //; rewrite H H0.
  apply/orP; case: j H H0 => j' H H0; [right | left];
    (rewrite mem_map; last by move => ? ? []).
  - by case: k H0 => // k' H0; rewrite (mem_iota 0 k'.+1).
  - by case: i H => // i' H; rewrite (mem_iota 0 i'.+1) leq0n ltnS.
Qed.

Definition range_finMixin :=
  Eval hnf in UniqFinMixin range_enum_uniq mem_range_enum.

Canonical range_finType := Eval hnf in FinType range range_finMixin.
Canonical range_subFinType := Eval hnf in [subFinType of range].

End Range.

(******************************************************************************)
(*  extensions for ssralg and ssrnum                                          *)
(******************************************************************************)

Section algebra_ext.

Variable (R : numDomainType).

Definition lter b : rel R := if b then Num.le else Num.lt.

Lemma lterE b r1 r2 :
  lter b r1 r2 = (if b then (r1 <= r2)%R else (r1 < r2)%R).
Proof. by rewrite /lter; case: b. Qed.

Lemma lternE b r1 r2 :
  lter (~~ b) r1 r2 = (if b then (r1 < r2)%R else (r1 <= r2)%R).
Proof. by rewrite /lter; case: b. Qed.

Lemma lter_opp2 b : {mono -%R%R : x y /~ lter b x y}.
Proof. by case: b => /= x y; rewrite (ltr_oppl, ler_oppl) opprK. Qed.

Lemma subr_lte0r b (x y : R) : lter b 0%R (y - x)%R = lter b x y.
Proof. by case: b => /=; rewrite (subr_ge0, subr_gt0). Qed.

Lemma addr_lte0r b (x y : R) : lter b 0%R (x + y)%R = lter b (- x)%R y.
Proof. by rewrite addrC -{1}(opprK x) subr_lte0r. Qed.

Lemma lter_trans b1 b2 r1 r2 r3 :
  lter b1 r1 r2 -> lter b2 r2 r3 -> lter (b1 && b2) r1 r3.
Proof.
  case: b1; case: b2 => /=.
  apply ler_trans. apply ler_lt_trans. apply ltr_le_trans. apply ltr_trans.
Qed.

Lemma lter_andb b1 b2 r1 r2 :
  lter (b1 && b2) r1 r2 = lter b1 r1 r2 && lter b2 r1 r2.
Proof.
  by case: b1; case: b2 => /=; rewrite ?ler_eqVlt;
    case: (_ < _)%R; rewrite ?(orbT, orbF, andbF, andbb).
Qed.

Lemma lter_orb b1 b2 r1 r2 :
  lter (b1 || b2) r1 r2 = lter b1 r1 r2 || lter b2 r1 r2.
Proof.
  by case: b1; case: b2 => /=; rewrite ?ler_eqVlt;
    case: (_ < _)%R; rewrite ?(orbT, orbF, orbb).
Qed.

Lemma lter_imply b1 b2 r1 r2 : b1 ==> b2 -> lter b1 r1 r2 -> lter b2 r1 r2.
Proof.
  by case: b1; case: b2 => //= _; rewrite ler_eqVlt => ->; rewrite orbT.
Qed.

Lemma lter_pmul2l b x : (0 < x)%R -> {mono *%R x : y z / lter b y z}.
Proof. by case: b => /= H y z; rewrite lter_pmul2l. Qed.

Lemma lter_pmul2r b x : (0 < x)%R -> {mono *%R^~ x : y z / lter b y z}.
Proof. by case: b => /= H y z; rewrite lter_pmul2r. Qed.

Lemma lter_nmul2l b x : (x < 0)%R -> {mono *%R x : y z /~ lter b y z}.
Proof. by case: b => /= H y z; rewrite lter_nmul2l. Qed.

Lemma lter_nmul2r b x : (x < 0)%R -> {mono *%R^~ x : y z /~ lter b y z}.
Proof. by case: b => /= H y z; rewrite lter_nmul2r. Qed.

(*
Lemma lter_wpmul2l b x : (0 < x)%R -> {homo *%R x : y z / lter b y z}.
Proof. by move/(lter_pmul2l b)/mono2W. Qed.

Lemma lter_wpmul2r b x : (0 < x)%R -> {homo *%R^~ x : y z / lter b y z}.
Proof. by move/(lter_pmul2r b)/mono2W. Qed.

Lemma lter_wnmul2l b x : (x < 0)%R -> {homo *%R x : y z /~ lter b y z}.
Proof. by move/(lter_nmul2l b)/mono2W. Qed.

Lemma lter_wnmul2r b x : (x < 0)%R -> {homo *%R^~ x : y z /~ lter b y z}.
Proof. by move/(lter_nmul2r b)/mono2W. Qed.
*)

Lemma lter_add2l b x : {mono +%R x : y z / lter b y z}.
Proof. by case: b => /= y z; rewrite lter_add2. Qed.

Lemma lter_add2r b x : {mono +%R^~ x : y z / lter b y z}.
Proof. by case: b => /= y z; rewrite lter_add2. Qed.

End algebra_ext.

Lemma lterN (R : realDomainType) b (r1 r2 : R) :
  ~~ (lter b r1 r2) = lter (~~ b) r2 r1.
Proof. by case: b => /=; rewrite -(lerNgt, ltrNge). Qed.

Lemma lter_pdivl_mulr (F : numFieldType) b (z x y : F) :
  (0 < z)%R -> lter b x (y / z)%R = lter b (x * z)%R y.
Proof. by case: b => H /=; rewrite lter_pdivl_mulr. Qed.

Lemma lter_pdivr_mulr (F : numFieldType) b (z x y : F) :
  (0 < z)%R -> lter b (y / z)%R x = lter b y (x * z)%R.
Proof. by case: b => H /=; rewrite lter_pdivr_mulr. Qed.

Lemma lter_pdivl_mull (F : numFieldType) b (z x y : F) :
  (0 < z)%R -> lter b x (z^-1 * y)%R = lter b (z * x)%R y.
Proof. by case: b => H /=; rewrite lter_pdivl_mull. Qed.

Lemma lter_pdivr_mull (F : numFieldType) b (z x y : F) :
  (0 < z)%R -> lter b (z^-1 * y)%R x = lter b y (z * x)%R.
Proof. by case: b => H /=; rewrite lter_pdivr_mull. Qed.

Lemma lter_ndivl_mulr (F : numFieldType) b (z x y : F) :
  (z < 0)%R -> lter b x (y / z)%R = lter b y (x * z)%R.
Proof. by case: b => H /=; rewrite lter_ndivl_mulr. Qed.

Lemma lter_ndivr_mulr (F : numFieldType) b (z x y : F) :
  (z < 0)%R -> lter b (y / z)%R x = lter b (x * z)%R y.
Proof. by case: b => H /=; rewrite lter_ndivr_mulr. Qed.

Lemma lter_ndivl_mull (F : numFieldType) b (z x y : F) :
  (z < 0)%R -> lter b x (z^-1 * y)%R = lter b y (z * x)%R.
Proof. by case: b => H /=; rewrite lter_ndivl_mull. Qed.

Lemma lter_ndivr_mull (F : numFieldType) b (z x y : F) :
  (z < 0)%R -> lter b (z^-1 * y)%R x = lter b (z * x)%R y.
Proof. by case: b => H /=; rewrite lter_ndivr_mull. Qed.

(******************************************************************************)
(*  extensions for interval                                                   *)
(******************************************************************************)

Notation itv1 := `]-oo, +oo[%R.
Notation itv0 := `]0, 0[%R.

Section interval_ext.

Variable (R : numDomainType).
Notation itv_bound := (itv_bound R).
Notation interval := (interval R).

Definition itv_lb (i : interval) := let: Interval lb _ := i in lb.
Definition itv_ub (i : interval) := let: Interval _ ub := i in ub.

Definition eq_itv_bound (b1 b2 : itv_bound) : bool :=
  match b1, b2 with
    | BOpen_if a x, BOpen_if b y => (a == b) && (x == y)
    | BInfty, BInfty => true
    | _, _ => false
  end.

Lemma eq_itv_boundP : Equality.axiom eq_itv_bound.
Proof.
  move => b1 b2; apply: (iffP idP).
  - by move: b1 b2 => [a x |] [b y |] => //= /andP [] /eqP -> /eqP ->.
  - by move => <-; case: b1 => //= a x; rewrite !eqxx.
Qed.

Canonical itv_bound_eqMixin := EqMixin eq_itv_boundP.
Canonical itv_bound_eqType := Eval hnf in EqType itv_bound itv_bound_eqMixin.

Definition eqitv (i1 i2 : interval) : bool :=
  let: Interval l1 u1 := i1 in
  let: Interval l2 u2 := i2 in (l1 == l2) && (u1 == u2).

Lemma eqitvP : Equality.axiom eqitv.
Proof.
  move => i1 i2; apply: (iffP idP).
  - by move: i1 i2 => [l1 u1] [l2 u2] => //= /andP [] /eqP -> /eqP ->.
  - by move => <-; case: i1 => /= l u; rewrite !eqxx.
Qed.

Canonical interval_eqMixin := EqMixin eqitvP.
Canonical interval_eqType := Eval hnf in EqType interval interval_eqMixin.

Lemma itv1E (x : R) : x \in itv1.
Proof. by []. Qed.

Lemma itv0E (x : R) : x \notin itv0.
Proof. by rewrite inE /= ltr_asym. Qed.

Definition itv_lelb (l1 l2 : itv_bound) : bool :=
  match l1, l2 with
  | BInfty, _ => true
  | _, BInfty => false
  | BOpen_if lb1 lr1, BOpen_if lb2 lr2 =>
    (lr1 == lr2) && (lb1 ==> lb2) || (lr1 < lr2)%R
  end.

Definition itv_leub (u1 u2 : itv_bound) : bool :=
  match u1, u2 with
  | _, BInfty => true
  | BInfty, _ => false
  | BOpen_if ub1 ur1, BOpen_if ub2 ur2 =>
    (ur1 == ur2) && (ub2 ==> ub1) || (ur1 < ur2)%R
  end.

Lemma itv_lelb_trans : transitive itv_lelb.
Proof.
  move => [lb1 lr1 |] [lb2 lr2 |] [lb3 lr3 |] //=.
  do 2 (let H := fresh "H" in
        case/orP; first case/andP => /eqP H; subst; move => H).
  - by rewrite eqxx /=; move: lb1 lb2 lb3 H H0 => [] [] [].
  - by rewrite H0 orbT.
  - by rewrite H orbT.
  - by rewrite (ltr_trans H H0) orbT.
Qed.

Lemma itv_leub_trans : transitive itv_leub.
Proof.
  move => [ub1 ur1 |] [ub2 ur2 |] [ub3 ur3 |] //=.
  do 2 (let H := fresh "H" in
        case/orP; first case/andP => /eqP H; subst; move => H).
  - by rewrite eqxx /=; move: ub1 ub2 ub3 H H0 => [] [] [].
  - by rewrite H0 orbT.
  - by rewrite H orbT.
  - by rewrite (ltr_trans H H0) orbT.
Qed.

Lemma eq_itv_lelb (l1 l2 : itv_bound) :
  l1 == l2 = (itv_lelb l1 l2 && itv_lelb l2 l1).
Proof.
  move: l1 l2 => [lb1 lr1 |] [lb2 lr2 |] => //=.
  by move: lb1 lb2 => [] [];
    rewrite !(andbT, andbF) -!ler_eqVlt /=
            (esym (eqr_le _ _), ltr_le_asym, ler_lt_asym).
Qed.

Lemma eq_itv_leub (u1 u2 : itv_bound) :
  u1 == u2 = (itv_leub u1 u2 && itv_leub u2 u1).
Proof.
  move: u1 u2 => [ub1 ur1 |] [ub2 ur2 |] => //=.
  by move: ub1 ub2 => [] [];
    rewrite !(andbT, andbF) -!ler_eqVlt /=
            (esym (eqr_le _ _), ltr_le_asym, ler_lt_asym).
Qed.

Definition itv_intersection (i1 i2 : interval) : interval :=
  let: Interval l1 u1 := i1 in
  let: Interval l2 u2 := i2 in
  Interval
    (if itv_lelb l1 l2 then l2 else l1)
    (if itv_leub u1 u2 then u1 else u2).

Definition itv_intersection1i : left_id itv1 itv_intersection.
Proof. by case => i []. Qed.

Definition itv_intersectioni1 : right_id itv1 itv_intersection.
Proof. by case => -[lb lr |] [ub ur |]. Qed.

Lemma itv_intersectionii : idempotent itv_intersection.
Proof. by case => -[lb lr |] [ub ur |] => //=; rewrite !eqxx !implybb. Qed.

Definition itv_isnot0 (i : interval) :=
  let: Interval l u := i in
  match l, u with
    | BOpen_if lb lr, BOpen_if ub ur => lter (~~ (lb || ub)) lr ur
    | _, _ => true
  end.

Definition itv_is0 (i : interval) := ~~ itv_isnot0 i.

Definition itv_eq (i1 i2 : interval) :=
  (i1 == i2) || (itv_is0 i1 && itv_is0 i2).

Definition itv_subset (i1 i2 : interval) :=
  (i1 == itv_intersection i1 i2) || itv_is0 i1.

End interval_ext.

Arguments itv1E {R} x.
Arguments itv0E {R} x.
Arguments itv_intersection {R} i1 i2.
Arguments itv_intersection1i {R} i : rename.
Arguments itv_intersectioni1 {R} i : rename.
Arguments itv_intersectionii {R} i : rename.
Arguments itv_isnot0 {R} i.
Arguments itv_is0 {R} i.
Arguments itv_eq {R} i1 i2.
Arguments itv_subset {R} i1 i2.

Lemma itv_isnot0P (R : numFieldType) (i : interval R) :
  reflect (exists x, x \in i) (itv_isnot0 i).
Proof.
  move: i => [] [lb lr |] [ub ur |] /=; apply (iffP idP) => //.
  - move => H; exists ((lr + ur) / 2%:R)%R; rewrite inE -!lternE.
    by rewrite lter_pdivr_mulr ?lter_pdivl_mulr ?pmulrn_lgt0 ?ltr01 //
               !mulrnAr !mulr1 /GRing.natmul lter_add2l lter_add2r
               -lter_andb -negb_or.
  - by case => x; rewrite inE -!lternE negb_or => /andP []; apply lter_trans.
  - move => _; exists (lr + 1)%R;
      rewrite inE -lternE andbT -{1}(addr0 lr) lter_add2l.
    by case: lb => //=; rewrite (ltr01, ler01).
  - move => _; exists (ur - 1)%R;
      rewrite inE -lternE -{2}(subr0 ur) lter_add2l lter_opp2 /=.
    by case: ub => //=; rewrite (ltr01, ler01).
  - by move => _; exists 0%R; rewrite inE.
Qed.

Lemma itv_is0P (R : numFieldType) (i : interval R) :
  reflect (forall x, x \notin i) (itv_is0 i).
Proof.
  apply (iffP negP).
  - by move => H x; apply/negP => H0; apply/H/itv_isnot0P; exists x.
  - by move => H /itv_isnot0P [x H0]; move: (H x); rewrite H0.
Qed.

Lemma itv_lelb_total (R : realDomainType) : total (@itv_lelb R).
Proof.
  move => [lb1 lr1 |] [lb2 lr2 |] => //=.
  by move: lb1 lb2 => [] []; case: (ltrgtP lr1 lr2).
Qed.

Lemma itv_leub_total (R : realDomainType) : total (@itv_leub R).
Proof.
  move => [ub1 ur1 |] [ub2 ur2 |] => //=.
  by move: ub1 ub2 => [] []; case: (ltrgtP ur1 ur2).
Qed.

Lemma itv_intersectionC (R : realDomainType) :
  commutative (@itv_intersection R).
Proof.
  move => [l1 u1] [l2 u2] /=; congr Interval; do 2 case: ifP => //=.
  - by move => H H0; apply/eqP; rewrite eq_itv_lelb H H0.
  - by case/orP: (itv_lelb_total l1 l2) => ->.
  - by move => H H0; apply/eqP; rewrite eq_itv_leub H H0.
  - by case/orP: (itv_leub_total u1 u2) => ->.
Qed.

Lemma itv_intersectionA (R : realDomainType) :
  associative (@itv_intersection R).
Proof.
  move => [l1 u1] [l2 u2] [l3 u3] /=; congr Interval;
    do ! case: ifP => //=; try congruence.
  - by move => H H0; rewrite (itv_lelb_trans H H0).
  - move => H H0 H1 _; apply/eqP; rewrite eq_itv_lelb H0 /=.
    move: (itv_lelb_total l1 l2); rewrite {}H /= => H.
    move: (itv_lelb_total l2 l3); rewrite {}H1 /= => H1.
    apply (itv_lelb_trans H1 H).
  - by move => H H0 H1; rewrite (itv_leub_trans H H1) in H0.
  - move => H H0 _ H1; apply/eqP; rewrite eq_itv_leub H1 /=.
    move: (itv_leub_total u1 u2); rewrite {}H /= => H.
    move: (itv_leub_total u2 u3); rewrite {}H0 /= => H0.
    apply (itv_leub_trans H0 H).
Qed.

Canonical itv_intersection_monoid (R : realDomainType) :=
  Monoid.Law (@itv_intersectionA R)
             (@itv_intersection1i R)
             (@itv_intersectioni1 R).

Canonical itv_intersection_comoid (R : realDomainType) :=
  Monoid.ComLaw (@itv_intersectionC R).

Lemma itv_intersectionE (R : realDomainType) (x : R) (i1 i2 : interval R) :
  x \in itv_intersection i1 i2 = (x \in i1) && (x \in i2).
Proof.
  move: i1 i2 => [l1 u1] [l2 u2]; rewrite !inE /=.
  by rewrite -andbA [X in _ = (_ && X)]andbCA andbA; congr andb;
    [move: {u1 u2} l1 l2 | move: {l1 l2} u1 u2];
    move => [[] r1 |] [[] r2 |] //=;
    rewrite (andbT, andbF) //= -?ler_eqVlt;
    (case: ifP; last move/negbT; rewrite -?(ltrNge, lerNgt) => H);
    match goal with
      |- ?p = _ => case_eq p; last move/negbT;
                   rewrite -/(is_true _) -?(ltrNge, lerNgt) => H0
    end;
    apply/esym; rewrite ?(andbT, andbF) //= -/(is_true _);
    match goal with
      | H : is_true (_ ?a ?b), H0 : is_true (_ ?b ?c) |- is_true (_ ?a ?c) =>
      move: (ler_trans H H0) || move: (ler_lt_trans H H0) ||
      move: (ltr_le_trans H H0) || move: (ltr_trans H H0)
    end;
    rewrite // ler_eqVlt => ->; rewrite orbT.
Qed.

Lemma itv_eqP (R : numFieldType) (i1 i2 : interval R) :
  reflect (forall x, x \in i1 <-> x \in i2) (itv_eq i1 i2).
Proof.
  apply (iffP idP).
  - case/orP; first by move/eqP => ->.
    by case/andP => /itv_isnot0P H /itv_isnot0P H0 x;
      split => H1; [case: H | case: H0]; exists x.
  - move => H; rewrite /itv_eq orbC -negb_or -implybE; apply/implyP.
    move: i1 i2 H.
    suff H0 (i1' i2' : interval R) :
      (forall x, x \in i1' <-> x \in i2') -> itv_isnot0 i1' -> i1' == i2'
      by move => i1 i2 H /orP [];
        last rewrite eq_sym; apply: H0 => // => x; apply iff_sym.
    move: i1' i2' => [l1 u1] [l2 u2] H H0; apply/eqP; congr Interval;
      [move: l1 l2 H H0 | move: u1 u2 H H0];
      move => [b1 r1 |] [b2 r2 |] //= H H0.
    + case: u1 H H0 => [ub1 ur1 |] //=.
Abort.

Lemma itv_subsetP (R : realFieldType) (i1 i2 : interval R) :
  reflect (forall x, x \in i1 -> x \in i2) (itv_subset i1 i2).
Proof.
  apply (iffP idP); first case/predU1P.
  - by move => -> x; rewrite itv_intersectionE; case/andP.
  - by move/itv_isnot0P => H x H0; case: H; exists x.
  - move => H; rewrite /itv_subset orbC -implybE;
      apply/implyP => /itv_isnot0P [] x H0.
Abort.

Lemma itv_intersection3E (R : realDomainType) (i1 i2 i3 : interval R) :
  exists x y, pred3 i1 i2 i3 x /\
              pred3 i1 i2 i3 y /\
              itv_intersection i1 (itv_intersection i2 i3) =
              itv_intersection x y.
Proof.
  move: i1 i2 i3 => [l1 u1] [l2 u2] [l3 u3] => /=.
  do ! case: ifP; move => H H0 H1 H2;
    match goal with
    | |- exists x y, _ /\ _ /\ Interval ?l ?u = _ =>
      match l with
      | l1 => exists (Interval l1 u1)
      | l2 => exists (Interval l2 u2)
      | l3 => exists (Interval l3 u3)
      end;
      match u with
      | u1 => exists (Interval l1 u1)
      | u2 => exists (Interval l2 u2)
      | u3 => exists (Interval l3 u3)
      end
    end;
    rewrite !eqxx /= ?orbT; do ! split => //;
    congr Interval; case: ifP => //= H3; try congruence; apply/eqP.
  - by rewrite eq_itv_lelb H2 H3.
  - by rewrite eq_itv_leub (itv_leub_trans H0 H) H3.
  - by rewrite eq_itv_lelb H2 H3.
  - by rewrite eq_itv_leub H0 H3.
  - by rewrite eq_itv_lelb H1 H3.
  - by rewrite eq_itv_leub H H3.
  - by rewrite eq_itv_lelb H2 H3.
  - by rewrite eq_itv_leub H0 H3.
  - by rewrite eq_itv_lelb H2 H3.
  - by rewrite (itv_leub_trans H3 H0) in H.
  - by rewrite (itv_lelb_trans H3 H1) in H2.
  - move: (itv_lelb_total l1 l2); rewrite H2 /= => H4.
    by rewrite (itv_lelb_trans H4 H3) in H1.
Qed.

Lemma itv_bigIE
      (I : eqType) (R : realDomainType) (r : seq I) (f : I -> interval R) :
  0 < size r ->
  exists i j, i \in r /\ j \in r /\
    \big[itv_intersection/itv1]_(i <- r) f i = itv_intersection (f i) (f j).
Proof.
  elim: r => //= k r IH _.
  rewrite big_cons.
  case: (ltnP 0 (size r)).
  - case/IH => i [j] [H] [H0] ->.
    case: (itv_intersection3E (f k) (f i) (f j)) => i1 [i2] [H1] [H2] ->.
    by move: H1 H2 => /or3P [] /eqP -> /or3P [] /eqP ->;
      do 2 eexists; do ? split; rewrite inE (eqxx, H, H0) (orTb, orbT).
  - case: r {IH} => //= _; exists k; exists k.
    do 2 (split; first by rewrite inE).
    by rewrite big_nil itv_intersectioni1 itv_intersectionii.
Qed.

Lemma itv_intersection_isnot0E
      (I : eqType) (R : realFieldType) (r : seq I) (f : I -> interval R) :
  itv_isnot0 (\big[itv_intersection/itv1]_(i <- r) f i) =
  all itv_isnot0 [seq itv_intersection (f i1) (f i2) | i1 <- r, i2 <- r].
Proof.
  set b := itv_isnot0 _.
  case_eq b; subst b.
  - move => H; apply/esym; move: H; rewrite -!/(is_true _) => H.
    apply/allP => /= x /allpairsP [] [i j] /= [Hi Hj ->] {x}.
    case/itv_isnot0P: H => x H; apply/itv_isnot0P; exists x.
    move: H.
    have/(eq_big_idem xpredT f itv_intersectionii) -> //= : r =i i :: j :: r
      by move => k; rewrite !inE;
                 do !case: eqP => //= ?; subst; rewrite (Hi, Hj).
    by rewrite !big_cons itv_intersectionA itv_intersectionE => /andP [].
  - move/negP => H0; apply/esym/negP => /allP H; apply: H0.
    case: (ltnP 0 (size r)).
    + case/(itv_bigIE f) => i [j] [H0] [H1] ->.
      by apply/H/allpairsP; exists (i, j); do ! split.
    + by case: r {H} => // _; rewrite big_nil.
Qed.

(******************************************************************************)
(*  extensions for matrix                                                     *)
(******************************************************************************)

Lemma trmxD (R : zmodType) m n : {morph @trmx R m n : x y / (x + y)%R}.
Proof. by move => x y; apply/matrixP => i j; rewrite !mxE. Qed.

Lemma trmx_scale (R : ringType) m n (a : R) :
  {morph @trmx _ m n : x / (a *: x)%R}.
Proof. by move => x; apply/matrixP => i j; rewrite !mxE. Qed.
