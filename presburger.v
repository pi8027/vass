Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp.
Require Import utils matrix_ext.
Import GroupScope GRing.Theory Num.Theory.

(******************************************************************************)
(*  Semilinear set and Presburger arithmetic                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Term and formula of Presburger arithmetic *)

Inductive term (v : nat) :=
  | t_const   of int
  | t_var     of 'I_v
  | t_add     of term v & term v
  | t_mulc    of int & term v.

Inductive formula (v : nat) :=
  | f_all     of formula (1 + v)
  | f_exists  of formula (1 + v)
  | f_neg     of formula v
  | f_and     of formula v & formula v
  | f_or      of formula v & formula v
  | f_imply   of formula v & formula v
  | f_leq     of term v & term v
  | f_lt      of term v & term v
  | f_eq      of term v & term v.

Fixpoint t_rename v v' (f : 'I_v -> 'I_v') (t : term v) : term v' :=
  match t with
    | t_const n => t_const v' n
    | t_var var => t_var (f var)
    | t_add t1 t2 => t_add (t_rename f t1) (t_rename f t2)
    | t_mulc n t => t_mulc n (t_rename f t)
  end.

Definition f_divisible v (n : nat) (t : term v) : formula v :=
  f_exists (@f_eq (1 + v) (t_mulc n (t_var 0%R)) (t_rename (@rshift 1 _) t)).

Check (@f_all 0 (f_all (f_leq (t_var (inord 1))
                              (t_add (t_var (inord 1)) (t_var (inord 0)))))).

(* Normal form of Prethburger formula *)

Inductive nformula (v : nat) :=
  | nf_exists of nformula (1 + v)
  | nf_neg    of nformula v
  | nf_and    of nformula v & nformula v
  | nf_or     of nformula v & nformula v
  | nf_leq    of 'cV[int]_v & int
  | nf_eq     of 'cV[int]_v & int.

(* Interpretation of Presburger arithmetic  *)

Fixpoint interpret_term fvs (t : term fvs) (assign : 'cV[int]_fvs) : int :=
  match t with
    | t_const n => n
    | t_var v => assign v 0%R
    | t_add t t' => interpret_term t assign + interpret_term t' assign
    | t_mulc n t => n * interpret_term t assign
  end.

Fixpoint interpret_formula fvs (f : formula fvs) : 'cV[int]_fvs -> Prop :=
  match f with
    | f_all f =>
      fun assign => forall n, interpret_formula f (col_mx (const_mx n) assign)
    | f_exists f =>
      fun assign => exists n, interpret_formula f (col_mx (const_mx n) assign)
    | f_neg f => fun assign => ~ interpret_formula f assign
    | f_and f f' =>
      fun assign => interpret_formula f assign /\ interpret_formula f' assign
    | f_or f f' =>
      fun assign => interpret_formula f assign \/ interpret_formula f' assign
    | f_imply f f' =>
      fun assign => interpret_formula f assign -> interpret_formula f' assign
    | f_leq t t' =>
      fun assign => (interpret_term t assign <= interpret_term t' assign)%R
    | f_lt t t' =>
      fun assign => (interpret_term t assign < interpret_term t' assign)%R
    | f_eq t t' =>
      fun assign => interpret_term t assign == interpret_term t' assign
  end.

Fixpoint interpret_nformula fvs (f : nformula fvs) : 'cV[int]_fvs -> Prop :=
  match f with
    | nf_exists f =>
      fun assign => exists n, interpret_nformula f (col_mx (const_mx n) assign)
    | nf_neg f => fun assign => ~ interpret_nformula f assign
    | nf_and f f' =>
      fun assign => interpret_nformula f assign /\ interpret_nformula f' assign
    | nf_or f f' =>
      fun assign => interpret_nformula f assign \/ interpret_nformula f' assign
    | nf_leq t n => fun assign => ((t^T *m assign) 0 0 <= n)%R
    | nf_eq t n  => fun assign => ((t^T *m assign) 0 0 == n)%R
  end.

(* Normal form computation *)

Fixpoint normal_t fvs (t : term fvs) : 'cV[int]_fvs * int :=
  (* a_1 x_1 + ... + a_n x_n + m *)
  match t with
    | t_const n => (0%R, (n : int))
    | t_var v => (\col_v' (v == v' : int), 0%R)%R
    | t_add t t' =>
      let: (cs, n) := normal_t t in
      let: (cs', m) := normal_t t' in (cs + cs', n + m)%R
    | t_mulc c t =>
      let: (cs, n) := normal_t t in (c *: cs, n * c)%R
  end.

Fixpoint normal_f fvs (f : formula fvs) : nformula fvs :=
  match f with
    | f_all f => nf_neg (nf_exists (nf_neg (normal_f f)))
    | f_exists f => nf_exists (normal_f f)
    | f_neg f => nf_neg (normal_f f)
    | f_and f f' => nf_and (normal_f f) (normal_f f')
    | f_or f f' => nf_or (normal_f f) (normal_f f')
    | f_imply f f' => nf_or (nf_neg (normal_f f)) (normal_f f')
    | f_leq t t' =>
      let: (cs, n) := normal_t t in
      let: (cs', m) := normal_t t' in
      nf_leq (cs - cs') (m - n)%R
    | f_lt t t' =>
      let: (cs, n) := normal_t t in
      let: (cs', m) := normal_t t' in
      nf_leq (cs - cs') (m - n - 1)%R
    | f_eq t t' =>
      let: (cs, n) := normal_t t in
      let: (cs', m) := normal_t t' in
      nf_eq (cs - cs') (m - n)%R
  end.

(* Correctness proof of normal form computation *)

Lemma nt_correct fvs (t : term fvs) assign :
  interpret_term t assign =
  (let (c, n) := normal_t t in (c^T *m assign) 0 0 + n)%R :> int.
Proof.
  elim: t assign => /=.
  - by move => n assign; rewrite trmx0 mul0mx mxE add0r.
  - move => v assign.
    rewrite addr0 !mxE (bigID (eq_op^~ v)) /= big_pred1_eq !mxE eqxx mul1r.
    apply/eqP; rewrite addrC -subr_eq addrN; apply/eqP.
    apply big_ind => //.
    + by move => x y <- <-.
    + by move => ? /negPf; rewrite !mxE eq_sym => -> /=; rewrite mul0r.
  - move => t; case_eq (normal_t t) => cs n _ IHt.
    move => t'; case_eq (normal_t t') => cs' m _ IHt' i.
    by rewrite trmxD mulmxDl mxE IHt IHt' !addrA (addrAC _ n).
  - move => c t; case_eq (normal_t t) => cs n H IH i.
    by rewrite trmx_scale -scalemxAl mxE -(mulrC c) -mulrDr -IH.
Qed.

Lemma nf_correct fvs (f : formula fvs) assign :
  (forall fvs (f : nformula fvs) assign,
    let P := interpret_nformula f assign in ~ ~ P -> P) ->
  (interpret_formula f assign <-> interpret_nformula (normal_f f) assign).
Proof.
  move => dne; move: fvs f assign; refine (formula_ind _ _ _ _ _ _ _ _ _).
  - move => fvs f IH assign; split => H.
    + by case => a; apply; apply IH, H.
    + by move => a; apply IH, dne => H0; apply H; exists a.
  - by move => fvs f IH assign; split; case => a H; exists a; apply IH.
  - by move => fvs f IH assign; split => H H0; apply H, IH.
  - by move => fvs f IHf f' IHf' assign; split;
      case => H H0; (split; [apply IHf | apply IHf']).
  - by move => fvs f IHf f' IHf' assign; split;
      (case => H; [left; apply IHf | right; apply IHf']).
  - move => fvs f IHf f' IHf' assign; split.
    + by move => H; apply dne => /= /Decidable.not_or [] /dne /IHf /H /IHf'.
    + by case => [H /IHf /H | H H0] //; apply IHf'.
  - move => /= fvs t t' assign; rewrite !nt_correct.
    case_eq (normal_t t); case_eq (normal_t t') => /= cs n _ cs' m _.
    by rewrite -ler_subr_addr -addrA addrC -ler_subl_addr
               trmxD trmxN mulmxBl (mxE addmx_key) (mxE oppmx_key).
  - move => /= fvs t t' assign; rewrite !nt_correct.
    case_eq (normal_t t); case_eq (normal_t t') => /= cs n _ cs' m _.
    by rewrite ler_sub_addr lez_addr1 -ltr_subr_addr -addrA addrC -ltr_subl_addr
               trmxD trmxN mulmxBl (mxE addmx_key) (mxE oppmx_key).
  - move => /= fvs t t' assign.
    rewrite !nt_correct.
    case_eq (normal_t t); case_eq (normal_t t') => /= cs n _ cs' m _.
    by rewrite eq_sym -subr_eq -addrA addrC eq_sym -subr_eq
               trmxD trmxN mulmxBl (mxE addmx_key) (mxE oppmx_key).
Qed.
