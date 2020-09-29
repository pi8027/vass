From mathcomp Require Import all_ssreflect all_algebra.
Import Order.TTheory GRing.Theory Num.Theory.

(******************************************************************************)
(*  extensions for bigop                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Semilattice.

Section Definitions.
Variables (T : Type).

Structure law := Law {
  operator : T -> T -> T;
  _ : associative operator;
  _ : commutative operator;
  _ : idempotent operator
}.
Local Coercion operator : law >-> Funclass.

Let op_id (op1 op2 : T -> T -> T) := phant_id op1 op2.

Definition clone_law op :=
  fun (opL : law) & op_id opL op =>
  fun opmA opmC opmI (opL' := @Law op opmA opmC opmI)
    & phant_id opL' opL => opL'.

End Definitions.

Module Import Exports.
Coercion operator : law >-> Funclass.
Notation "[ 'semilattice' 'of' f ]" := (@clone_law _ _ f _ id _ _ _ id)
  (at level 0, format"[ 'semilattice'  'of'  f ]") : form_scope.
End Exports.

Module Theory.

Section Theory.
Variable (T : Type).

Section Plain.
Variable join : law T.
Lemma joinA : associative join. Proof. by case join. Qed.
Lemma joinC : commutative join. Proof. by case join. Qed.
Lemma joinI : idempotent join. Proof. by case join. Qed.
Lemma joinCA : left_commutative join.
Proof. by move=> x y z; rewrite !joinA (joinC x). Qed.
Lemma joinAC : right_commutative join.
Proof. by move=> x y z; rewrite -!joinA (joinC y). Qed.
Lemma joinACA : interchange join join.
Proof. by move=> x y z t; rewrite -!joinA (joinCA y). Qed.
End Plain.

End Theory.

End Theory.
Include Theory.

End Semilattice.
Export Semilattice.Exports.

Section PervasiveSemilattices.

Variable (disp : unit) (T : latticeType disp).

Canonical maxr_semilattice :=
  Semilattice.Law (@joinA _ T) (@joinC _ T) (@joinxx _ T).
Canonical minr_semilattice :=
  Semilattice.Law (@meetA _ T) (@meetC _ T) (@meetxx _ T).

End PervasiveSemilattices.

Section SemilatticeProperties.

Import Semilattice.Theory.

Variable R : Type.

Variable (idx : R) (join : Semilattice.law R).
Notation "0" := idx.
Notation "||%L" := join (at level 0).
Notation "x || y" := (join x y).

Lemma big_join0 I r (P : pred I) F :
  0 || \big[||%L/0]_(i <- r | P i) F i =
  \big[||%L/0]_(i <- r | P i) F i.
Proof.
rewrite unlock; elim: r => /= [| i r <-]; first by rewrite joinI.
by case P; rewrite 1?joinCA (joinA _ 0 0) joinI.
Qed.

Lemma big0_eq I r (P : pred I) : \big[||%L/0]_(i <- r | P i) 0 = 0.
Proof.
by rewrite big_const_seq; elim: (count _ _) => //= n ->; rewrite joinI.
Qed.

Lemma big0 I r (P : pred I) F :
  (forall i, P i -> F i = 0) -> \big[||%L/0]_(i <- r | P i) F i = 0.
Proof. move/(eq_bigr _) ->; apply: big0_eq. Qed.

Lemma big0_seq (I : eqType) r (P : pred I) F :
    (forall i, P i && (i \in r) -> F i = 0) ->
  \big[||%L/0]_(i <- r | P i) F i = 0.
Proof. by move=> eqF1; rewrite big_seq_cond big_andbC big0. Qed.

Lemma big_mkcond_l I r (P : pred I) F :
  \big[||%L/0]_(i <- r | P i) F i =
     \big[||%L/0]_(i <- r) (if P i then F i else 0).
Proof.
elim: r => /= [| i r IH]; first by rewrite !big_nil.
by rewrite !big_cons {}IH; case: (P); rewrite // big_join0.
Qed.

Lemma big_mkcondr_l I r (P Q : pred I) F :
  \big[||%L/0]_(i <- r | P i && Q i) F i =
     \big[||%L/0]_(i <- r | P i) (if Q i then F i else 0).
Proof. by rewrite -big_filter_cond big_mkcond_l big_filter. Qed.

Lemma big_mkcondl_l I r (P Q : pred I) F :
  \big[||%L/0]_(i <- r | P i && Q i) F i =
     \big[||%L/0]_(i <- r | Q i) (if P i then F i else 0).
Proof. by rewrite big_andbC big_mkcondr_l. Qed.

Lemma big_cat_l I r1 r2 (P : pred I) F :
  \big[||%L/0]_(i <- r1 ++ r2 | P i) F i =
     (\big[||%L/0]_(i <- r1 | P i) F i || \big[||%L/0]_(i <- r2 | P i) F i).
Proof.
rewrite !(big_mkcond_l _ P); elim: r1 => /= [|i r1 IH].
- by rewrite big_nil big_join0.
- by rewrite !big_cons IH joinA.
Qed.

Lemma big_pred1_eq_l (I : finType) (i : I) F :
  \big[||%L/0]_(j | j == i) F j = F i || 0.
Proof. by rewrite -big_filter filter_index_enum enum1 unlock. Qed.

Lemma big_pred1_l (I : finType) i (P : pred I) F :
  P =1 pred1 i -> \big[||%L/0]_(j | P j) F j = F i || 0.
Proof. by move/(eq_bigl _ _)->; apply: big_pred1_eq_l. Qed.

Lemma big_cat_nat_l n m p (P : pred nat) F : m <= n -> n <= p ->
  \big[||%L/0]_(m <= i < p | P i) F i =
  (\big[||%L/0]_(m <= i < n | P i) F i) ||
  (\big[||%L/0]_(n <= i < p | P i) F i).
Proof.
move=> le_mn le_np.
by rewrite -big_cat_l -{2}(subnKC le_mn) -iota_add subnDA subnKC // leq_sub.
Qed.

Lemma big_nat_recr_l n m F : m <= n ->
  \big[||%L/0]_(m <= i < n.+1) F i = (\big[||%L/0]_(m <= i < n) F i) || F n.
Proof.
move=> lemn; rewrite (@big_cat_nat_l n) ?leqnSn //.
rewrite (big_ltn (leqnn n.+1)) (big_geq (leqnn n.+1)).
by rewrite joinC -joinA big_join0 joinC.
Qed.

Lemma big_ord_recr_l n F :
  \big[||%L/0]_(i < n.+1) F i =
     (\big[||%L/0]_(i < n) F (widen_ord (leqnSn n) i)) || F ord_max.
Proof.
transitivity (\big[||%L/0]_(0 <= i < n.+1) F (inord i)).
  by rewrite big_mkord; apply: eq_bigr => i _; rewrite inord_val.
rewrite big_nat_recr_l // big_mkord; congr (_ || F _); last first.
  by apply: val_inj; rewrite /= inordK.
by apply/eq_bigr => [] i _; congr F; apply: ord_inj; rewrite inordK //= leqW.
Qed.

Lemma big_sumType_l (I1 I2 : finType) (P : pred (I1 + I2)) F :
  \big[||%L/0]_(i | P i) F i =
         (\big[||%L/0]_(i | P (inl _ i)) F (inl _ i))
      || (\big[||%L/0]_(i | P (inr _ i)) F (inr _ i)).
Proof.
Abort.

Lemma big_split_ord_l m n (P : pred 'I_(m + n)) F :
  \big[||%L/0]_(i | P i) F i =
         (\big[||%L/0]_(i | P (lshift n i)) F (lshift n i))
      || (\big[||%L/0]_(i | P (rshift m i)) F (rshift m i)).
Proof.
rewrite -(big_map (lshift n) P F) -(big_map (@rshift m _) P F).
rewrite -big_cat_l; congr bigop; apply: (inj_map val_inj).
rewrite /index_enum -!enumT val_enum_ord map_cat -map_comp val_enum_ord.
rewrite -map_comp (map_comp (addn m)) val_enum_ord.
by rewrite -iota_addl addn0 iota_add.
Qed.

Lemma big_flatten_l I rr (P : pred I) F :
  \big[||%L/0]_(i <- flatten rr | P i) F i
    = \big[||%L/0]_(r <- rr) \big[||%L/0]_(i <- r | P i) F i.
Proof.
by elim: rr => [|r rr IHrr]; rewrite ?big_nil //= big_cat_l big_cons -IHrr.
Qed.

Lemma eq_big_perm_l (I : eqType) r1 r2 (P : pred I) F :
    perm_eq r1 r2 ->
  \big[||%L/0]_(i <- r1 | P i) F i = \big[||%L/0]_(i <- r2 | P i) F i.
Proof.
move/permP; rewrite !(big_mkcond_l _ P).
elim: r1 r2 => [|i r1 IHr1] r2 eq_r12.
  by case: r2 eq_r12 => // i r2; move/(_ (pred1 i)); rewrite /= eqxx.
have r2i: i \in r2 by rewrite -has_pred1 has_count -eq_r12 /= eqxx.
case/splitPr: r2 / r2i => [r3 r4] in eq_r12 *; rewrite big_cat_l /= !big_cons.
rewrite joinCA; congr (_ || _); rewrite -big_cat_l; apply: IHr1 => a.
move/(_ a): eq_r12; rewrite !count_cat /= addnCA; exact: addnI.
Qed.

Lemma big_uniq_l (I : finType) (r : seq I) F :
  uniq r -> \big[||%L/0]_(i <- r) F i = \big[||%L/0]_(i in r) F i.
Proof.
move=> uniq_r; rewrite -(big_filter _ (mem r)); apply: eq_big_perm_l.
by rewrite filter_index_enum uniq_perm ?enum_uniq // => i; rewrite mem_enum.
Qed.

Lemma big_rem_l (I : eqType) r x (P : pred I) F :
    x \in r ->
  \big[||%L/0]_(y <- r | P y) F y
    = (if P x then F x else 0) || \big[||%L/0]_(y <- rem x r | P y) F y.
Proof.
by move/perm_to_rem/(eq_big_perm_l _)->; rewrite !(big_mkcond_l _ P) big_cons.
Qed.

Lemma big_undup_l (I : eqType) (r : seq I) (P : pred I) F :
  \big[||%L/0]_(i <- undup r | P i) F i = \big[||%L/0]_(i <- r | P i) F i.
Proof.
rewrite -!(big_filter _ P) filter_undup.
elim: {P r}(filter P r) => //= i r IHr.
case: ifP => [r_i | _]; rewrite !big_cons {}IHr //.
by rewrite (big_rem_l _ _ r_i) joinA joinI.
Qed.

Lemma eq_big_idem_l (I : eqType) (r1 r2 : seq I) (P : pred I) F :
  r1 =i r2 ->
  \big[||%L/0]_(i <- r1 | P i) F i = \big[||%L/0]_(i <- r2 | P i) F i.
Proof.
move=> eq_r; rewrite -big_undup_l // -(big_undup_l r2) //; apply/eq_big_perm_l.
by rewrite uniq_perm ?undup_uniq // => i; rewrite !mem_undup eq_r.
Qed.

Lemma big_undup_iterop_count_l (I : eqType) (r : seq I) (P : pred I) F :
  \big[||%L/0]_(i <- undup r | P i) iterop (count_mem i r) ||%L (F i) 0
    = \big[||%L/0]_(i <- r | P i) F i.
Proof.
Abort.

Lemma big_split_l I r (P : pred I) F1 F2 :
  \big[||%L/0]_(i <- r | P i) (F1 i || F2 i) =
    \big[||%L/0]_(i <- r | P i) F1 i || \big[||%L/0]_(i <- r | P i) F2 i.
Proof.
by elim/big_rec3: _ => [|i x y _ _ ->]; rewrite ?joinI // joinCA -!joinA joinCA.
Qed.

Lemma bigU_l (I : finType) (A B : pred I) F :
  \big[||%L/0]_(i in [predU A & B]) F i =
    (\big[||%L/0]_(i in A) F i) || (\big[||%L/0]_(i in B) F i).
Proof.
elim: index_enum => [| x xs IH]; rewrite ?big_nil ?big_cons ?joinI //.
by rewrite !inE IH; do 2 case: (_ \in _) => //=;
  rewrite 1?joinACA ?joinI // !joinA // (joinC _ (F x)).
Qed.

Lemma bigID_l I r (a P : pred I) F :
  \big[||%L/0]_(i <- r | P i) F i =
    \big[||%L/0]_(i <- r | P i && a i) F i ||
    \big[||%L/0]_(i <- r | P i && ~~ a i) F i.
Proof.
rewrite !(big_mkcond_l _ _ F) -big_split_l;
  elim: r => /= [| i r IH]; first by rewrite !big_nil.
by rewrite !big_cons; case a; case: (P) => //=;
  rewrite -IH ?joinI // -joinA ?(joinCA _ 0) big_join0.
Qed.
Arguments bigID_l [I r].

Lemma bigD1_l (I : finType) j (P : pred I) F :
  P j -> \big[||%L/0]_(i | P i) F i = F j || \big[||%L/0]_(i | P i) F i.
Proof.
move=> Pj.
rewrite -{2}big_join0 joinA -(big_pred1_l (P := pred1 j)) // -bigU_l.
apply/eq_bigl => i; do !rewrite unfold_in /= -?eqE.
by case: eqP Pj => //= <- ->.
Qed.
Arguments bigD1_l [I j P F].

End SemilatticeProperties.
