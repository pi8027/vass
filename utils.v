From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp.
Import GroupScope GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Lemma split_lshift (m n : nat) (i : 'I_m) : split (lshift n i) = inl i.
Proof. by apply: unsplitK (inl i). Qed.

Lemma split_rshift (m n : nat) (i : 'I_n) : split (rshift m i) = inr i.
Proof. by apply: unsplitK (inr i). Qed.
*)

Lemma lshift_inj (m n : nat) : injective (@lshift m n).
Proof. by move => x y /(f_equal val) /= /val_inj. Qed.

Lemma rshift_inj (m n : nat) : injective (@rshift m n).
Proof. by move => x y /(f_equal val) /= /addnI /val_inj. Qed.

Lemma lshift_rshift_neq (m n : nat) i j : lshift m i <> rshift n j.
Proof. by apply/eqP; rewrite eqE /= neq_ltn (ltn_addr _ (ltn_ord i)). Qed.

Lemma rshift_lshift_neq (m n : nat) i j : rshift n j <> lshift m i.
Proof. by move/esym/lshift_rshift_neq. Qed.

Lemma enum_rank_in_inj
      (T : finType) (x y : T) (A : pred T) (H : x \in A) (H0 : y \in A) :
  enum_rank_in H x = enum_rank_in H0 y -> x = y.
Proof. move/(congr1 enum_val); by do 2 rewrite enum_rankK_in //. Qed.

Lemma all_allpairsP (S T : eqType) (R : Type)
                    (g : pred R) (f : S -> T -> R) (s : seq S) (t : seq T) :
  reflect (forall (i : S) (j : T), i \in s -> j \in t -> g (f i j))
          (all g [seq f i j | i <- s, j <- t]).
Proof.
apply (iffP idP); elim: s t => // s ss IHs; elim => [| t ts IHt] //=.
- rewrite /= all_cat => /and3P [H H0 H1] x y /=.
  rewrite !inE => /orP [/eqP -> | H2] /orP [/eqP -> | H3] //;
    try (apply IHt => //; last by rewrite ?(inE, eqxx) ?H2 ?orbT);
    try by (apply (IHs (t :: ts)) => //; rewrite ?(inE, eqxx)).
  + rewrite /= all_cat H0 /=.
    elim: ss H1 {IHs IHt} => //= s' ss IHs /andP [H4].
    by rewrite !all_cat => /andP [-> H5] /=; apply IHs.
  + rewrite /= all_cat H0 /=.
    elim: ss H1 {IHs IHt H2} => //= s' ss IHs /andP [H4].
    by rewrite !all_cat => /andP [-> H5] /=; apply IHs.
- by move => {IHs} _; elim: ss.
- move => H; apply/andP; split; first by apply H; rewrite inE eqxx.
  rewrite all_cat; apply/andP; split.
Abort.

Lemma all_allpairsP (S T R : eqType)
                    (g : pred R) (f : S -> T -> R) (s : seq S) (t : seq T) :
  reflect (forall (i : S) (j : T), i \in s -> j \in t -> g (f i j))
          (all g [seq f i j | i <- s, j <- t]).
Proof.
apply (iffP allP).
- by move => H i j H0 H1; apply/H/allpairsP; exists (i, j).
- by move => H x /allpairsP [] [i j] [] /= H0 H1 ->; apply H.
Qed.

Lemma all_pmap S T (p : pred T) (f : S -> option T) xs :
  all p (pmap f xs) = all (fun i => oapp p true (f i)) xs.
Proof. by elim: xs => //= x xs <-; case: (f x). Qed.

Lemma all_filter S (p q : pred S) xs :
  all p (filter q xs) = all (fun i => q i ==> p i) xs.
Proof. by elim: xs => //= x xs <-; case: (q x). Qed.

Lemma all_enum (T : finType) (P : pred T) : all P (enum T) = [forall i, P i].
Proof.
apply/idP; case: ifP; first by move/forallP => H; apply/allP.
by move/negP => H /allP H0; apply: H;
  apply/forallP => x; apply: H0; rewrite mem_enum.
Qed.
