From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth.
From iRRAM.lang Require Import proofmode notation extraction.
Require Import Reals Fourier.
Set Default Proof Using "Type".

Axiom Rpower_0_lt: forall r1 r2 (R1: 0 < r1),
    0 < Rpower r1 r2.

Ltac ria0 := try fourier; try ring; try field.

Ltac ria1 :=
  match goal with
  | [H: context[Rpower _ (- _)] |- _] =>
    erewrite Rpower_Ropp in H
  | [|- context[Rpower _ (- _)]] =>
    erewrite Rpower_Ropp

  | [H: context[Rmult _ 1] |- _] =>
    erewrite Rmult_1_r in H
  | [|- context[Rmult _ 1]] =>
    erewrite Rmult_1_r

  | [H: context[IZR (_ + _)] |- _] =>
    rewrite plus_IZR in H
  | [|- context[IZR (_ + _)]] =>
    rewrite plus_IZR

  | [H: context[IZR (_ - _)] |- _] =>
    rewrite minus_IZR in H
  | [|- context[IZR (_ - _)]] =>
    rewrite minus_IZR

  | [H: context[Rpower _ (_ + _)] |- _] =>
    rewrite Rpower_plus in H
  | [|- context[Rpower _ (_ + _)]] =>
    rewrite Rpower_plus
  | [H: context[Rpower _ (_ - _)] |- _] =>
    rewrite Rpower_plus in H
  | [|- context[Rpower _ (_ - _)]] =>
    rewrite Rpower_plus

  | [H: context[(?r - ?r)%R] |- _] =>
    rewrite (@Rminus_diag_eq r r); [|auto; fail]
  | [|- context[(?r - ?r)%R]] =>
    rewrite (@Rminus_diag_eq r r); [|auto; fail]

  | [|- 0 < Rpower _ _] =>
    apply Rpower_0_lt

  | [H: context[Rpower _ 0] |- _] =>
    try erewrite Rpower_O in H; [|ria0]
  | [|- context[Rpower _ 0]] =>
    try erewrite Rpower_O; [|ria0]

  | [H: context[Rpower _ 1] |- _] =>
    try erewrite Rpower_1 in H; [|ria0]
  | [|- context[Rpower _ 1]] =>
    try erewrite Rpower_1; [|ria0]
  end.

Ltac ria := repeat (try ria1; simpl in *; auto; ria0).

Lemma move_lt_rhs (a b c:R)
      (H: a < b + c): a - c < b.
Proof.
  apply Rlt_minus in H. apply Rminus_lt. ria.
Qed.

Lemma Rmult_minus_distr_r (r1 r2 r3: R):
  (r1 - r2) * r3 = r1 * r3 - r2 * r3.
Proof.
  rewrite Rmult_comm. rewrite Rmult_minus_distr_l. ring.
Qed.
