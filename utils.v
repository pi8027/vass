From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma lshift_inj (m n : nat) : injective (@lshift m n).
Proof. by move=> x y /(f_equal val) /= /val_inj. Qed.

Lemma rshift_inj (m n : nat) : injective (@rshift m n).
Proof. by move=> x y /(f_equal val) /addnI /val_inj. Qed.

Lemma lshift_rshift_neq (m n : nat) i j : lshift m i != rshift n j.
Proof. by rewrite eqE /= neq_ltn ltn_addr. Qed.

Lemma rshift_lshift_neq (m n : nat) i j : rshift n j != lshift m i.
Proof. by rewrite eq_sym; exact: lshift_rshift_neq. Qed.

Lemma enum_rank_in_inj
      (T : finType) (x0 y0 : T) A (Ax0 : x0 \in A) (Ay0 : y0 \in A) :
  {in A &, forall x y, enum_rank_in Ax0 x = enum_rank_in Ay0 y -> x = y}.
Proof. by move=> x y xA yA /(congr1 enum_val); rewrite !enum_rankK_in. Qed.

Lemma all_allpairsP
      (S : eqType) (T : S -> eqType) (R : Type)
      (g : pred R) (f : forall i : S, T i -> R)
      (s : seq S) (t : forall i : S, seq (T i)) :
  reflect (forall (i : S) (j : T i), i \in s -> j \in t i -> g (f i j))
          (all g [seq f i j | i <- s, j <- t i]).
Proof.
elim: s => [|x s IHs]; first by constructor.
rewrite /= all_cat all_map /preim.
apply/(iffP andP)=> [[/allP /= ? ? x' y x'_in_xs]|p_xs_t].
  by move: x'_in_xs y; rewrite inE => /predU1P [-> //|? ?]; exact: IHs.
split; first by apply/allP => ?; exact/p_xs_t/mem_head.
by apply/IHs => x' y x'_in_s; apply: p_xs_t; rewrite inE x'_in_s orbT.
Qed.

Lemma all_pmap S T (p : pred T) (f : S -> option T) xs :
  all p (pmap f xs) = all (fun i => oapp p true (f i)) xs.
Proof. by elim: xs => //= x xs <-; case: (f x). Qed.

Lemma all_filter S (p q : pred S) xs :
  all p (filter q xs) = all (fun i => q i ==> p i) xs.
Proof. by elim: xs => //= x xs <-; case: (q x). Qed.

Lemma all_enum (T : finType) (P : pred T) : all P (enum T) = [forall i, P i].
Proof.
apply/allP/forallP => H x; move: (H x); rewrite mem_enum inE //; exact.
Qed.
